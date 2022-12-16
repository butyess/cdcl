use std::collections::HashMap;
use std::collections::HashSet;

use priority_queue::PriorityQueue;

use super::model::{Var, Lit};

#[derive(Debug)]
pub struct CVSIDS {
    variables: PriorityQueue<Var, i32>, // use a heap/priority queue
    signs: HashMap<Var, bool>,
}

impl CVSIDS {
    pub fn new(variables: &HashSet<Var>) -> CVSIDS {
        CVSIDS {
            variables: variables.iter().map(|x| (x.clone(), 0)).collect(),
            signs: HashMap::new(),
        }
    }

    pub fn get_highest_score_variable(&mut self) -> Lit {
        let (var, _) = self.variables.pop()
            .expect("Asked top literal but the prioirty queue is empty");

        let sign = match self.signs.get(&var) {
            None => { self.signs.insert(var.clone(), true); true },
            Some(b) => *b
        };

        if sign {
            i32::try_from(var).unwrap()
        } else {
            -i32::try_from(var).unwrap()
        }
    }

    pub fn propagated_variable(&mut self, var: Var) {
        self.variables.remove(&var);
    }

    // pub fn revert_variable(&mut self, var: Var) {
    //     self.variables.push(var, 0);
    // }

    // pub fn decay(&mut self) {}

    // pub fn bump(&mut self) {}

}


