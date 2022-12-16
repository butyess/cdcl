use std::rc::Rc;
use std::collections::HashMap;
use std::collections::HashSet;

use super::model::Lit;
use super::model::Clause;

pub struct WatchedLiterals {
    clauses: HashMap<Rc<Clause>, Vec<Lit>>,
    literals: HashMap<Lit, (Vec<Rc<Clause>>, Vec<Rc<Clause>>)>,
}

impl WatchedLiterals {
    pub fn new(clauses: &Vec<Rc<Clause>>, literals: &HashSet<Lit>) -> WatchedLiterals {
        WatchedLiterals {
            clauses: clauses.iter().map(|c| (Rc::clone(c), Vec::new())).collect(),
            literals: literals.iter().map(|l| (Lit::clone(l), (Vec::new(), Vec::new()))).collect(),
        }
    }
}
