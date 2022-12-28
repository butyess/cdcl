use std::collections::{HashMap, HashSet};
use std::ops::Shr;

use priority_queue::PriorityQueue;

use crate::model::{Var, Lit};

#[derive(Debug)]
pub struct CVSIDS {
    variables: PriorityQueue<Var, u32>,
    signs: HashMap<Var, bool>,
    bump_const: u32,
    decay_inverse: f32,
}

impl CVSIDS {
    pub fn new(variables: &HashSet<Var>) -> CVSIDS {
        CVSIDS {
            variables: variables.iter().map(|&x| (x, 0)).collect(),
            signs: HashMap::new(),
            bump_const: 1,
            decay_inverse: 6.0 / 5.0,
        }
    }

    pub fn pick_literal(&mut self) -> Lit {
        let (var, _) = self.variables.pop()
            .expect("Asked top literal but the prioirty queue is empty");

        let sign = match self.signs.get(&var) {
            None => { self.signs.insert(var, true); true },
            Some(b) => *b
        };

        if sign {
            var as Lit
        } else {
            panic!("can't pick a negative literal");
            // var.checked_neg().unwrap() as Lit
        }
    }

    pub fn propagated_variable(&mut self, var: &Var) {
        self.variables.remove(var);
    }

    pub fn revert_variable(&mut self, var: &Var) {
        self.variables.push(*var, *var);
    }

    pub fn decay(&mut self) {
        self.bump_const = ((self.decay_inverse * self.bump_const as f32).ceil()) as u32;
    }

    fn scale_all_priorities(&mut self, amount: u32) {
        for (_var, prio) in self.variables.iter_mut() {
            *prio = prio.shr(amount);
        }
    }

    pub fn bump(&mut self, var: &Var) {
        if let Some(prio) =  self.variables.get_priority(var) {
            match prio.checked_add(self.bump_const) {
                Some(newprio) => { self.variables.change_priority(var, newprio); }
                None => {
                    self.scale_all_priorities(10);
                    self.variables.change_priority(var, self.variables.get_priority(var).unwrap() + self.bump_const);
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;
    use super::*;

    #[test]
    fn test_cvsids_keep_sign() {
        let mut cvsids = CVSIDS::new(&HashSet::from([1, 2, 3, 4]));
        cvsids.bump(&1);
        assert_eq!(cvsids.pick_literal(), 1);
        cvsids.revert_variable(&1);
        cvsids.bump(&1);
        assert_eq!(cvsids.pick_literal(), 1);
    }

    #[test]
    fn test_cvsids_propagate_variable() {
        let mut cvsids = CVSIDS::new(&HashSet::from([1, 2, 3, 4]));
        cvsids.bump(&1);
        cvsids.bump(&2);
        cvsids.bump(&2);
        cvsids.propagated_variable(&2);
        assert_eq!(cvsids.pick_literal(), 1);
    }

    #[test]
    fn test_cvsids_revert_variable() {
        let mut cvsids = CVSIDS::new(&HashSet::from([1, 2, 3, 4]));
        cvsids.bump(&1);
        assert_eq!(cvsids.pick_literal(), 1);
        cvsids.bump(&2);
        cvsids.revert_variable(&1);
        assert_eq!(cvsids.pick_literal(), 2);
    }

    #[test]
    fn test_cvsids_decay() {
        let mut cvsids = CVSIDS::new(&HashSet::from([1]));
        cvsids.decay();
        cvsids.bump(&1);
        assert_eq!(*cvsids.variables.get_priority(&1).unwrap(), 2);
    }

    #[test]
    fn simple_test_cvsids() {
        let mut cvsids = CVSIDS::new(&HashSet::from([1, 2, 3, 4]));
        cvsids.bump(&1);
        assert_eq!(cvsids.pick_literal(), 1);
        cvsids.bump(&3);
        assert_eq!(cvsids.pick_literal(), 3);
        cvsids.propagated_variable(&4);
        assert_eq!(cvsids.pick_literal(), 2);
    }

    #[test]
    fn test_not_fail_cvsids() {
        let mut cvsids = CVSIDS::new(&HashSet::from([1, 2, 3, 4]));
        cvsids.bump(&1);
        cvsids.pick_literal();
        cvsids.bump(&1);
    }

    #[test]
    fn test_not_fail_cvsids_2() {
        let mut cvsids = CVSIDS::new(&HashSet::from([1, 2, 3, 4]));
        cvsids.bump(&1);
        cvsids.bump(&2);
        cvsids.bump(&3);
        cvsids.bump(&4);
        cvsids.bump(&5);
    }

    #[test]
    fn test_cvsids_bump_overflow() {
        let mut cvsids = CVSIDS::new(&HashSet::from([1, 2]));
        cvsids.bump(&1);
        println!("{:?}", cvsids.variables);

        cvsids.bump_const = u32::MAX;
        cvsids.bump(&1);
        println!("{:?}", cvsids.variables);

        cvsids.scale_all_priorities(10);
        println!("{:?}", cvsids.variables);

        let x = u32::MAX.shr(10);
        let prio = cvsids.variables.get_priority(&1).unwrap();

        assert_eq!(x, *prio);
    }
}
