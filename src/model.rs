pub mod decision_stack;
pub mod cvsids;

use std::collections::HashMap;
use std::collections::HashSet;
use std::rc::Rc;

use self::decision_stack::DecisionStack;
use self::cvsids::CVSIDS;

pub type Lit = i32;
pub type Clause = Vec<Lit>;

pub struct Model {
    clauses: Vec<Rc<Clause>>,
    variables: Vec<Rc<Lit>>,

    variables_state: HashMap<Rc<Lit>, bool>, // assigned or not
    unit_clauses: HashMap<Rc<Clause>, Rc<Lit>>,
    decision_stack: DecisionStack,
    vsids: CVSIDS,
}

impl Model {
    fn unique_variables(clauses: &Vec<Clause>) -> HashSet<Lit> {
        clauses.iter().flatten().map(i32::clone).collect()
    }

    pub fn new(clauses: Vec<Clause>) -> Model {
        let variables = Model::unique_variables(&clauses);
        let variablesrc: Vec<Rc<Lit>> = variables.into_iter().map(Rc::new).collect();

        let vsids: CVSIDS = CVSIDS::new(&variablesrc);
        let vstate: HashMap<Rc<Lit>, bool> = variablesrc.iter().map(|x| (Rc::clone(x), false)).collect();

        Model {
            clauses: clauses.into_iter().map(Rc::new).collect(),
            variables: variablesrc,

            variables_state: vstate,
            unit_clauses: HashMap::new(),
            decision_stack: DecisionStack::new(),
            vsids: vsids,
        }
    }

    // implement these functions
    // TODO: Rc<Lit> is not okay, for example it's hard to do i32::abs, but also you don't need it
    //       because i32 is very small.

    /*
    fn unit_propagation() -> Option<(Rc<Clause>, Rc<Lit>)> { }

    fn all_variables_assigned(&self) -> bool {
        self.decision_stack.len_decided_variables() == self.variables.len()
    }

    fn make_decision(&mut self) {
        // ask VSIDS for decision (check if variable already assigned)
        let mut lit: Rc<Lit> = self.vsids.get_highest_score_variable();
        while variables_state.get(lit.abs()).unwrap() == true {
            lit = self.vsids.get_second_highest_score_variable();
        }

        // edit decision stack
        let units = self.decision_stack.decision(lit);
    }

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

        while !self.all_variables_assigned() {

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

