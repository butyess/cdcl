use std::collections::HashMap;
use crate::types::{Var, Lit, Sign};
use fastrand;

#[derive(Eq, PartialEq)]
#[derive(Debug)]
pub enum SignPolicy { Pos, Neg, Rnd }

impl SignPolicy {
    fn pick_sign(&self) -> Sign {
        match self {
            SignPolicy::Pos => Sign::Pos,
            SignPolicy::Neg => Sign::Neg,
            SignPolicy::Rnd => {
                match fastrand::bool() {
                    true => Sign::Pos,
                    false => Sign::Neg,
                }
            }
        }
    }
}

#[derive(Debug)]
pub struct VarOrder {
    vars        : Vec<Var>,
    activity    : HashMap<Var, f64>,
    signs       : HashMap<Var, Sign>,
    chosen      : HashMap<Var, bool>,
    bump        : f64,                  // initialized to 1.0
    inv_decay   : f64,
    counter     : usize,
    policy      : SignPolicy,           // default: choose only positive literals
}

impl VarOrder {
    pub fn new(decay: f64) -> VarOrder {
        VarOrder {
            vars: Vec::new(),
            activity: HashMap::new(),
            signs: HashMap::new(),
            chosen: HashMap::new(),
            bump: 1.0,
            inv_decay: 1.0 / decay,
            counter: 0,
            policy: SignPolicy::Pos,
        }
    }

    pub fn set_policy(&mut self, policy: SignPolicy) {
        self.policy = policy;
    }

    pub fn set_decay(&mut self, decay: f64) {
        self.inv_decay = 1.0 / decay;
    }

    pub fn new_var(&mut self, var: Var) {
        if !self.activity.contains_key(&var) {
            self.vars.push(var);
            self.activity.insert(var, 0.0);
            self.chosen.insert(var, false);
        }
    }

    pub fn bump(&mut self, var: Var) {
        let val: &mut f64 = self.activity.get_mut(&var).expect("No variable found");
        *val += self.bump;
        if *self.activity.get(&var).unwrap() > 1e100 {
            self.rescale();
        }
    }

    fn rescale(&mut self) {
        for val in self.activity.values_mut() {
            *val = *val * 1e-100;
        }
        self.bump *= 1e-100;
    }

    pub fn decay(&mut self) {
        self.bump *= self.inv_decay;
    }

    fn sort_vars(&mut self) {
        self.vars.sort_unstable_by(|a, b| {
            let av = self.activity.get(a).unwrap();
            let bv = self.activity.get(b).unwrap();
            av.partial_cmp(bv).unwrap().reverse()
        });
    }

    pub fn pick(&mut self) -> Lit {
        self.counter += 1;
        if self.counter % 50 == 0 {
            self.sort_vars();
        }

        let var = *self.vars.iter()
            .find(|v| !self.chosen.get(v).unwrap())
            .unwrap();

        self.chosen.insert(var, true);

        if !self.signs.contains_key(&var) {
            self.signs.insert(var, self.policy.pick_sign());
        }

        match self.signs.get(&var) {
            Some(Sign::Pos) => var.to_lit(Sign::Pos),
            Some(Sign::Neg) => var.to_lit(Sign::Neg),
            _ => panic!(""),
        }
    }

    pub fn undo(&mut self, var: Var) {
        self.chosen.insert(var, false);
    }

    pub fn selected(&mut self, var: Var) {
        self.chosen.insert(var, true);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_vorder_sort() {
        let mut vorder = VarOrder::new(0.95);
        vorder.new_var(Var::from_u32(1));
        vorder.new_var(Var::from_u32(2));
        vorder.new_var(Var::from_u32(3));
        vorder.bump(Var::from_u32(3));
        vorder.bump(Var::from_u32(3));
        vorder.bump(Var::from_u32(3));
        vorder.bump(Var::from_u32(2));
        vorder.sort_vars();
        assert_eq!(vorder.vars, [3, 2, 1].into_iter().map(Var::from_u32).collect::<Vec<Var>>());
    }

    #[test]
    fn test_vorder_keep_sign() {
        let mut vorder = VarOrder::new(0.95);
        vorder.new_var(Var::from_u32(1));
        vorder.new_var(Var::from_u32(2));
        vorder.new_var(Var::from_u32(3));
        vorder.new_var(Var::from_u32(4));
        vorder.bump(Var::from_u32(1));
        vorder.sort_vars();
        assert_eq!(vorder.pick(), Lit::from_i32(1));
        vorder.undo(Var::from_u32(1));
        vorder.bump(Var::from_u32(1));
        assert_eq!(vorder.pick(), Lit::from_i32(1));
    }

    #[test]
    fn test_vorder_propagate_variable() {
        let mut vorder = VarOrder::new(0.95);
        vorder.new_var(Var::from_u32(1));
        vorder.new_var(Var::from_u32(2));
        vorder.bump(Var::from_u32(1));
        vorder.bump(Var::from_u32(2));
        vorder.bump(Var::from_u32(2));
        vorder.sort_vars();
        vorder.selected(Var::from_u32(2));
        assert_eq!(vorder.pick(), Lit::from_i32(1));
    }

    #[test]
    fn test_vorder_revert_variable() {
        let mut vorder = VarOrder::new(0.95);
        vorder.new_var(Var::from_u32(1));
        vorder.new_var(Var::from_u32(2));
        vorder.bump(Var::from_u32(1));
        vorder.sort_vars();
        assert_eq!(vorder.pick(), Lit::from_i32(1));
        vorder.bump(Var::from_u32(2));
        vorder.sort_vars();
        vorder.selected(Var::from_u32(1));
        assert_eq!(vorder.pick(), Lit::from_i32(2));
    }

    #[test]
    fn simple_test_vorder() {
        let mut vorder = VarOrder::new(0.95);
        vorder.new_var(Var::from_u32(1));
        vorder.new_var(Var::from_u32(2));
        vorder.new_var(Var::from_u32(3));
        vorder.new_var(Var::from_u32(4));
        vorder.bump(Var::from_u32(1));
        vorder.sort_vars();
        assert_eq!(vorder.pick(), Lit::from_i32(1));
        vorder.bump(Var::from_u32(3));
        vorder.bump(Var::from_u32(3));
        vorder.sort_vars();
        println!("vars: {:?}", vorder.vars);
        println!("activities: {:?}", vorder.activity);
        assert_eq!(vorder.pick(), Lit::from_i32(3));
        vorder.selected(Var::from_u32(4));
        assert_eq!(vorder.pick(), Lit::from_i32(2));
    }

    #[test]
    fn test_not_fail_vorder() {
        let mut vorder = VarOrder::new(0.95);
        vorder.new_var(Var::from_u32(1));
        vorder.new_var(Var::from_u32(2));
        vorder.new_var(Var::from_u32(3));
        vorder.new_var(Var::from_u32(4));
        vorder.bump(Var::from_u32(1));
        vorder.sort_vars();
        assert_eq!(vorder.pick(), Lit::from_i32(1));
        vorder.bump(Var::from_u32(1));
        vorder.sort_vars();
    }

    #[test]
    fn test_not_fail_vorder_2() {
        let mut vorder = VarOrder::new(0.95);
        vorder.new_var(Var::from_u32(1));
        vorder.new_var(Var::from_u32(2));
        vorder.new_var(Var::from_u32(3));
        vorder.new_var(Var::from_u32(4));
        vorder.bump(Var::from_u32(1));
        vorder.sort_vars();
        vorder.selected(Var::from_u32(1));
        vorder.bump(Var::from_u32(1));
        vorder.sort_vars();
    }
}
