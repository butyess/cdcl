use std::collections::HashMap;
use std::collections::HashSet;

use priority_queue::PriorityQueue;

use super::model::{Var, Lit};

#[derive(Debug)]
pub struct CVSIDS {
    variables: PriorityQueue<Var, i32>, // use a heap/priority queue
    signs: HashMap<Var, Option<bool>>,
}

impl CVSIDS {
    pub fn new(variables: &HashSet<Var>) -> CVSIDS {
        CVSIDS {
            variables: variables.iter().map(|x| (Var::clone(x), 0)).collect(),
            signs: variables.iter().map(|x| (Var::clone(x), None)).collect(),
        }
    }

    // pub fn get_highest_score_variable(&self) -> Lit { }

    // pub fn decay(&mut self) {}
    // pub fn bump(&mut self) {}
}


