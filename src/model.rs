use std::collections::HashSet;
use std::ops::Neg;
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
            println!("Propagating {:?}", &clauserc);
            let out = self.decision_stack.propagate(&clauserc, lit);
            self.vsids.propagated_variable(u32::try_from(lit.abs()).unwrap());
            println!("Decision stack: {}", self.decision_stack);
            match out {
                Left(mut units) => { self.unit_clauses.append(&mut units); }
                Right(conflict) => { return Some(conflict); }
            }
        }
        None
    }

    fn make_decision(&mut self) -> Option<Rc<Clause>> {
        let decided_lit = self.vsids.get_highest_score_variable();
        let out = self.decision_stack.decide(decided_lit);
        match out {
            Left(mut units) => { self.unit_clauses.append(&mut units); }
            Right(conflict) => { return Some(conflict); }
        }
        None
    }

    fn resolution(&self, base: &Clause, with: &Rc<Clause>) -> Clause {
        let mut result = Vec::new();

        base.iter()
            .filter(|l| !with.contains(&l.neg()))
            .for_each(|l| result.push(*l));

        with.iter()
            .filter(|l| !base.contains(&l.neg()) & !base.contains(l))
            .for_each(|l| result.push(*l));

        result
    }

    fn resolve_conflict(&mut self, orig_conflict: Rc<Clause>) {
        // 1. resolve until assertion
        let mut conflict: Clause = orig_conflict.to_vec();

        let assertion_literal: i32;
        loop {
            println!("Trying to resolve {:?}", &conflict);
            match self.decision_stack.find_assertion_literal(&conflict) {
                Some(al) => { assertion_literal = al; break; }
                None => {
                    let new_conflict = conflict.iter()
                        .map(|x| self.decision_stack.find_justification(&-x))
                        .filter_map(|x| x)
                        .next()
                        .map(|j| self.resolution(&conflict, j))
                        .expect("No justification found in current level");

                    conflict = new_conflict;
                }
            }
        }

        println!("Found assertion literal: {}", &assertion_literal);

        // 2. learn
        // bump vsids score
        for lit in conflict.iter() {
            self.vsids.bump(&(lit.abs() as u32));
        }
        let clauserc = Rc::new(conflict);
        self.clauses.push(Rc::clone(&clauserc));
        self.decision_stack.learn_clause(Rc::clone(&clauserc), &-assertion_literal);

        // 3. backjump: search level in decision stack,
        //              revert decision of all literals after the level,
        //              propagate the negated of assertion literal

        let non_assert_literals: HashSet<Lit> = clauserc.iter()
            .filter(|&l| *l != assertion_literal)
            .map(i32::clone)
            .collect();

        let rev_lit = self.decision_stack.search_backjump(&assertion_literal, &non_assert_literals);

        println!("Reverted literals: {:?}", rev_lit);

        for l in rev_lit {
            self.vsids.revert_variable(Var::try_from(l.abs()).unwrap())
        }

        match self.decision_stack.propagate(&clauserc, -assertion_literal) {
            Left(units) => { self.unit_clauses = units; }
            Right(_conflict) => { panic!("Got conflict {:?} right after backjumping", _conflict); }
        }
    }

    pub fn solve(&mut self) -> bool {
        if let Some(_conflict) = self.unit_propagation() {
            println!("Conflict during initial unit propagation");
            return false;
        }

        while !self.decision_stack.all_variables_assigned() {
            // a decision never bring to a conflict, given that the last
            // operation has been unit propagations
            if let Some(conflict) = self.make_decision() {
                println!("Found conflict after decision: {:?}", &conflict);

                self.vsids.decay();

                if self.decision_stack.level() <= 1 {
                    println!("Conflict on empty decision stack!");
                    return false;
                } else {
                    println!("Resolving conflict");
                    self.resolve_conflict(conflict);
                    println!("Decision stack after resolving conflict: {}", self.decision_stack);
                }

            }

            // println!("Decision stack: {}", self.decision_stack);
            // println!("Unit clauses: {:?}", self.unit_clauses);

            if let Some(conflict) = self.unit_propagation() {
                println!("Found conflict after propagation: {:?}", &conflict);

                self.vsids.decay();

                if self.decision_stack.level() <= 1 {
                    println!("Conflict on empty decision stack!");
                    return false;
                } else {
                    println!("Resolving conflict");
                    self.resolve_conflict(conflict);
                    println!("Decision stack after resolving conflict: {}", self.decision_stack);
                }
            }
        }

        return true;
    }

}

