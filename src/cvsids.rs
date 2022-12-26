use std::collections::HashMap;

use priority_queue::PriorityQueue;

use crate::model::{Var, Lit};

pub struct CVSIDS<'a> {
    variables: PriorityQueue<&'a Var, u32>,
    signs: HashMap<&'a Var, bool>,
    bump_const: u32,
    decay_inverse: f32,
}

impl<'a> CVSIDS<'a> {
    pub fn new<I>(variables: &I) -> CVSIDS
    where I: Iterator<Item = &'a Var>,
    {
        CVSIDS {
            variables: variables.map(|x| (x, 0)).collect(),
            signs: HashMap::new(),
            bump_const: 1,
            decay_inverse: 5.0 / 6.0,
        }
    }

    pub fn pick_literal(&mut self) -> Lit {
        let (var, _) = self.variables.pop()
            .expect("Asked top literal but the prioirty queue is empty");

        let sign = match self.signs.get(var) {
            None => { self.signs.insert(var, true); true },
            Some(b) => *b
        };

        if sign {
            *var as Lit
        } else {
            var.checked_neg().unwrap() as Lit
        }
    }

    pub fn propagated_variable(&mut self, var: &Var) {
        self.variables.remove(var);
    }

    pub fn revert_variable(&mut self, var: &Var) {
        self.variables.push(var, 0);
    }

    fn scale_all_priorities(&mut self, amount: u32) {
        for (_v, p) in self.variables.iter_mut() {
            *p = p.checked_shr(amount).unwrap();
        }
    }

    pub fn decay(&mut self) {
        self.bump_const = ((self.decay_inverse * self.bump_const as f32).ceil()) as u32;
    }

    pub fn bump(&mut self, var: &Var) {
        let mut overflow = false;

        self.variables.change_priority_by(var, |p| {
            match p.checked_mul(self.bump_const) {
                Some(out) => { *p = out; }
                None => { overflow = true; }
            }
        });

        if overflow {
            self.scale_all_priorities(10);
            self.bump(var);
        }

    }

}
