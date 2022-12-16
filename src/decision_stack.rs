use std::rc::Rc;
use std::collections::HashSet;

use super::model::Lit;
use super::model::Clause;
use super::watched_literals::WatchedLiterals;

pub struct DecisionStack {
    ds: Vec<Vec<(Rc<Lit>, Option<Rc<Clause>>)>>,
    wl: WatchedLiterals,
}

impl DecisionStack {
    pub fn new(clauses: &Vec<Rc<Clause>>, literals: &HashSet<Lit>) -> DecisionStack {
        DecisionStack {
            ds: Vec::new(),
            wl: WatchedLiterals::new(clauses, literals),
        }
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

