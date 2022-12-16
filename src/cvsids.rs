use std::collections::HashMap;
use std::collections::HashSet;

use priority_queue::PriorityQueue;

use super::model::Lit;

pub struct CVSIDS {
    variables: PriorityQueue<Lit, i32>, // use a heap/priority queue
    signs: HashMap<Lit, Option<bool>>,
}

impl CVSIDS {
    pub fn new(variables: &HashSet<Lit>) -> CVSIDS {
        CVSIDS {
            variables: variables.iter().map(|x| (Lit::clone(x), 0)).collect(),
            signs: variables.iter().map(|x| (Lit::clone(x), None)).collect(),
        }
    }

    // pub fn get_highest_score_variable(&self) -> Rc<Lit> {}
    // pub fn decay(&mut self) {}
    // pub fn bump(&mut self) {}
}


