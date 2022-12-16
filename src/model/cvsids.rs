use std::rc::Rc;
use std::collections::HashMap;

use priority_queue::PriorityQueue;

use super::Lit;

pub struct CVSIDS {
    variables: PriorityQueue<Rc<Lit>, i32>, // use a heap/priority queue
    signs: HashMap<Rc<Lit>, Option<bool>>,
}

impl CVSIDS {
    pub fn new(variables: &Vec<Rc<Lit>>) -> CVSIDS {
        CVSIDS {
            variables: variables.iter().map(|x| (Rc::clone(x), 0)).collect(),
            signs: variables.iter().map(|x| (Rc::clone(x), None)).collect(),
        }
    }

    // pub fn get_highest_score_variable(&self) -> Rc<Lit> {}
    // pub fn decay(&mut self) {}
    // pub fn bump(&mut self) {}
}


