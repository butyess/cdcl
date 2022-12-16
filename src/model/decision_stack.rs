use std::rc::Rc;

use super::Lit;
use super::Clause;

pub struct DecisionStack {
    ds: Vec<Vec<(Rc<Lit>, Option<Rc<Clause>>)>>,
}

impl DecisionStack {
    pub fn new() -> DecisionStack {
        DecisionStack { ds: Vec::new() }
    }


    /*
    pub fn propagate(
        &mut self,
        lit: Rc<Lit>,
        clause: Rc<Clause>
    ) -> Either<Vec<(Rc<Lit>, Rc<Clause)>,
                (Rc<Clause>, Rc<Lit>)> {}

    pub fn decision(&mut self, lit: Rc<Lit>) -> Vec<(Rc<Lit>, Rc<Clause))>

    pub fn len_decided_variables(&self) -> usize
    */
}

