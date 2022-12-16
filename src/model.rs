use std::collections::HashSet;
use std::rc::Rc;

use either::{Left, Right};

use super::decision_stack::DecisionStack;
use super::cvsids::CVSIDS;

pub type Var = u32;
pub type Lit = i32;
pub type Clause = Vec<Lit>;

#[derive(Debug)]
pub struct Model {
    pub clauses: Vec<Rc<Clause>>,
    pub variables: HashSet<Var>,
    pub unit_clauses: Vec<(Rc<Clause>, Lit)>,
    pub decision_stack: DecisionStack,
    pub vsids: CVSIDS,
}

impl Model {
    pub fn new(clauses: Vec<Clause>) -> Model {
        let variables: HashSet<Var> = clauses.iter().flatten().map(|x| u32::try_from(x.abs()).unwrap()).collect();
        let clauses: Vec<Rc<Clause>> = clauses.into_iter().map(Rc::new).collect();
        let vsids: CVSIDS = CVSIDS::new(&variables);
        let decision_stack: DecisionStack = DecisionStack::new(&clauses, &variables);

        Model {
            clauses: clauses,
            variables: variables,
            unit_clauses: Vec::new(),
            decision_stack: decision_stack,
            vsids: vsids,
        }
    }

    pub fn unit_propagation(&mut self) -> Option<Rc<Clause>> {
        while let Some((clauserc, lit)) = self.unit_clauses.pop() {
            dbg!(&clauserc);
            let out = self.decision_stack.propagate(&clauserc, lit);
            dbg!(&out);
            match out {
                Left(mut units) => { self.unit_clauses.append(&mut units); }
                Right(conflict) => { return Some(conflict); }
            }
        }
        None
    }

    // fn make_decision(&mut self) {
    //     let decided_lit = self.vsids.get_highest_score_variable();
    //     let mut units = self.decision_stack.decide(decided_lit);
    //     self.unit_clauses.append(&mut units);
    // }

    /* 
    fn resolve_conflict(&mut self, clause: Rc<Clause>, lit: Rc<Lit>) {
        1. resolve until assertion
        2. learn
        3. search level to backjump
        4. backjump
    }

    pub fn solve(&mut self) -> bool {
        if let Some(conflict) = self.unit_propagation() {
            return false;
        }

        while !self.ds.all_variables_assigned() {

            // a decision never bring to a conflict, given that the last stack
            // operations were unit propagations
            self.make_decision();

            if let Some(conflict) = self.unit_propagation() {
                match self.resolve_conflict(conflict) {
                    true => { continue; }
                    false => { return false; }
                }
            }
        }

        return true;
    }
    */

}

