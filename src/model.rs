use std::collections::{HashSet, HashMap, VecDeque};
use std::rc::Rc;

use log::{debug};

// use either::{Either, Left, Right, map};
use either::*;

use crate::watched_literals::WatchedLiterals;
use crate::cvsids::CVSIDS;

pub type Var = u32;
pub type Lit = i32;
pub type Clause = Vec<Lit>;

#[derive(Debug)]
#[derive(Eq, PartialEq)]
pub enum VarState { Positive, Negative, Undefined, }

pub type ConflictClause = Clause;
pub type UnitClauses = VecDeque<(Rc<Clause>, Lit)>;

#[derive(Debug)]
enum SolverState { Propagating(UnitClauses), Resolving(ConflictClause) }

pub type Assignment = HashMap<Var, VarState>;
type DecisionStack = Vec<(i32, Lit, Option<Rc<Clause>>)>;
pub type ResolutionProof = Vec<(Clause, Clause, Clause)>;

fn resolution(left: &Clause, right: &Clause) -> Clause {
    let mut newclause = Clause::new();
    for l in left {
        if !right.contains(&-l) { newclause.push(*l); }
    }
    for r in right.iter() {
        if !left.contains(&-r) && !left.contains(r) {
            newclause.push(*r);
        }
    }
    newclause
}


pub struct Model {
    clauses: Vec<Rc<Clause>>,
    variables: HashSet<Var>,
    decision_stack: DecisionStack,
    dl: i32,
    assignment: Assignment,
    proof: ResolutionProof,
    cvsids: CVSIDS,
    watched_literals: WatchedLiterals,
}

impl Model {

    pub fn new(
        init_clauses: Vec<Clause>
    ) -> Model {

        let clauses: Vec<Rc<Clause>> = init_clauses.into_iter()
            .map(Rc::new)
            .collect();

        let mut variables: HashSet<Var> = HashSet::new();
        clauses.iter()
            .for_each(|c| {
                c.iter().for_each(|v| { variables.insert(v.abs() as Var); })
            });

        let assignment = variables.iter()
            .map(|&v| (v, VarState::Undefined))
            .collect();

        let decision_stack = Vec::new();

        let cvsids = CVSIDS::new(&variables);
        let watched_literals = WatchedLiterals::new(&clauses, &variables);

        Model {
            clauses,
            variables,
            dl: 0,
            decision_stack,
            assignment,
            proof: Vec::new(),
            cvsids,
            watched_literals,
        }
    }

    fn reset(self) -> Model {
        Model {
            clauses: self.clauses.clone(),
            variables: self.variables.clone(),
            dl: 0,
            decision_stack: Vec::new(),
            assignment: self.variables.iter().map(|&v| (v, VarState::Undefined)).collect(),
            proof: Vec::new(),
            cvsids: CVSIDS::new(&self.variables),
            watched_literals: WatchedLiterals::new(&self.clauses, &self.variables),
        }
    }

    fn revert(
        &mut self,
        lit: &Lit
    ) {
        let val = self.assignment.get_mut(&(lit.abs() as Var)).unwrap();
        *val = VarState::Undefined;
    }

    fn decide(
        &mut self,
        dl: i32,
        lit: &Lit,
        justification: Option<Rc<Clause>>
    ) {
        // update decision stack
        self.decision_stack.push((dl, *lit, justification));

        // update assignments
        let val = self.assignment.get_mut(&(lit.abs() as Var)).unwrap();
        *val = if lit.is_positive() { VarState::Positive } else { VarState::Negative };
    }

    fn get_assertion_lit(
        &self,
        clause: &Clause,
        dl: &i32
    ) -> Option<Lit> {
        let last_level_lits: Vec<&Lit> = self.decision_stack.iter()
            .filter(|(lev, lit, _)| *lev == *dl && clause.contains(&-lit))
            .map(|(_, lit, _)| lit)
            .collect();

        debug!("current level literal of conflict clause found: {:?}", last_level_lits);

        match last_level_lits.len() {
            0 => { panic!("No literal found in last level while checking for assertion clause"); }
            1 => Some(**last_level_lits.first().unwrap()),
            _ => None,
        }
    }

    fn backjump(
        &mut self,
        assertion_literal: &Lit,
        assertion_clause: &Rc<Clause>
    ) -> SolverState {
        // learn (1)
        self.watched_literals.learn_clause(Rc::clone(&assertion_clause), &-assertion_literal);
        self.cvsids.decay();

        // backjump
        let non_assert_lits: HashSet<&Lit> = assertion_clause.iter()
            .filter(|&l| l != &-assertion_literal)
            .collect();

        while let Some((level, lit, justification)) = self.decision_stack.pop() {

            if level == 0 {
                self.decision_stack.push((level, lit, justification));
                break;
            }

            let non_assert_in_last_level = self.decision_stack.iter()
                .rev()
                .take_while(|(l, _, _)| *l == level)
                .any(|(_, x, _)| non_assert_lits.contains(&-x));

            if non_assert_in_last_level || non_assert_lits.contains(&-lit) {
                self.decision_stack.push((level, lit, justification));
                break;
            } else {
                self.revert(&lit);
                self.cvsids.revert_variable(&(lit.abs() as Var));

                while let Some((levl, l, j)) = self.decision_stack.pop() {
                    if levl != level {
                        self.decision_stack.push((levl, l, j));
                        break;
                    } else {
                        self.revert(&l);
                        self.cvsids.revert_variable(&(l.abs() as Var));
                    }
                }
            }

            // if non_assert_lits.contains(&-lit) {
            //     self.decision_stack.push((level, lit, justification));
            //     break;
            // } else {
            //     self.revert(&lit);
            //     self.cvsids.revert_variable(&(lit.abs() as Var));
            // }
        }

        // bump
        assertion_clause.iter()
            .for_each(|l| self.cvsids.bump(&(l.abs() as Var)));

        if let Some((level, _, _)) =
            self.decision_stack.last() {
            self.dl = *level;
        } else {
            self.dl = 0;
        }

        self.decide(self.dl, &-assertion_literal, Some(Rc::clone(&assertion_clause)));
        self.cvsids.propagated_variable(&(assertion_literal.abs() as Var));

        match self.watched_literals.decision(&-assertion_literal, &self.assignment) {
            Left(confl) => SolverState::Resolving(confl),
            Right(units) => SolverState::Propagating(units)
        }
    }

    fn resolve(&mut self, conflict: &Clause) -> SolverState {
        let mut j: Option<Rc<Clause>> = None;

        // resolve
        for (_, lit, just) in self.decision_stack.iter().rev() {
            if conflict.contains(&-lit) {
                j = just.clone();
                break;
            }
        }

        let justification = j.expect("Found no justification");

        let new_clause = resolution(conflict, &justification);

        debug!("resolving: {conflict:?} + {justification:?} = {new_clause:?}");
        self.proof.push((conflict.clone(), justification.to_vec(), new_clause.clone()));

        SolverState::Resolving(new_clause)
    }

    pub fn solve(mut self) -> Either<ResolutionProof, Assignment> {
        let mut max_conflicts: i32 = 100;
        let mut status: Option<bool> = None;

        while status.is_none() {
            status = self.search(max_conflicts);
            max_conflicts = ((max_conflicts as f32) * 1.5) as i32;
            self = self.reset();
            println!("too many conflict, resetting...")
        }

        match status.unwrap() {
            false => Left(self.proof),
            true => Right(self.assignment),
        }
    }

    // pub fn search(&mut self, max_conflicts: i32) -> Option<Either<&ResolutionProof, &Assignment>> {
    pub fn search(&mut self, max_conflicts: i32) -> Option<bool> {


        let mut nof_conflicts: i32 = 0;

        if !self.decision_stack.is_empty() || self.dl != 0 {
            panic!("can't start solving because decision stack is not empty");
        }

        let mut unit_clauses: VecDeque<(Lit, Rc<Clause>)> = self.clauses.iter()
            .filter(|&c| c.len() == 1)
            .map(|c| (c[0], Rc::clone(c)))
            .collect();

        // initial unit propagation
        while let Some((lit, clause)) = unit_clauses.pop_front() {
            if *self.assignment.get(&(lit.abs() as Var)).unwrap() != VarState::Undefined {
                continue;
            }

            self.decide(self.dl, &lit, Some(clause));
            self.cvsids.propagated_variable(&(lit.abs() as Var));

            match self.watched_literals.decision(&lit, &self.assignment) {
                Left(_conflict) => { return Some(false); },
                Right(units) => {
                    for (uc, l) in units {
                        unit_clauses.push_back((l, Rc::clone(&uc)))
                    }
                }
            }
        }

        while self.decision_stack.len() < self.variables.len() {

            if nof_conflicts > max_conflicts {
                return None;
            }

            let picked_lit = self.cvsids.pick_literal();
            self.dl += 1;
            self.decide(self.dl, &picked_lit, None);

            debug!("decided literal: {picked_lit}");

            let mut solver_state =
                match self.watched_literals.decision(&picked_lit, &self.assignment) {
                    Left(conflict) => SolverState::Resolving(conflict),
                    Right(units) => SolverState::Propagating(units)
                };

            loop {

                debug!("starting loop iteration. decision stack:");
                for l in self.decision_stack.iter() {
                    debug!("{l:?}");
                }
                // debug!("watched literals:");
                // debug!("{}", self.watched_literals);
                debug!("solver state: {solver_state:?}");

                match &mut solver_state {
                    SolverState::Resolving(conflict) => {
                        debug!("conflict, clause: {conflict:?}");

                        if self.dl == 0 { return Some(false); }

                        if let Some(assertion_lit) =
                            self.get_assertion_lit(&conflict, &self.dl) {
                            debug!("found assertion literal: {assertion_lit}. now backjumping...");
                            let conflict_rc = Rc::new(conflict.clone());
                            solver_state = self.backjump(&assertion_lit, &conflict_rc);
                            self.clauses.push(conflict_rc);

                            if let SolverState::Resolving(_) = solver_state {
                                nof_conflicts += 1;
                            }

                        } else {
                            solver_state = self.resolve(&conflict);
                        }
                    },
                    SolverState::Propagating(units) => {
                        debug!("propagating...");

                        if let Some((uc, lit)) = units.pop_front() {
                            if *self.assignment.get(&(lit.abs() as Var)).unwrap() != VarState::Undefined {
                                continue;
                            }

                            self.decide(self.dl, &lit, Some(uc));
                            self.cvsids.propagated_variable(&(lit.abs() as Var));

                            debug!("propagated {lit}");

                            match &mut self.watched_literals.decision(&lit, &self.assignment) {
                                Left(conflict) => {
                                    nof_conflicts += 1;
                                    solver_state = SolverState::Resolving(conflict.clone());
                                },
                                Right(new_units) => {
                                    units.append(new_units);
                                }
                            }
                        } else {
                            debug!("no more propagation to be done!");
                            break;
                        }
                    }
                }
            }
        }

        Some(true)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_backjumping_2() {

        let mut model = Model::new(vec![
            vec![1],
            vec![2],
        ]);

        model.decide(0, &1, Some(Rc::clone(&model.clauses[0])));

        println!("initial decision stack:");
        for l in model.decision_stack.iter() {
            println!("{:?}", l);
        }

        model.backjump(&2, &Rc::new(vec![2]));

        println!("final decision stack:");
        for l in model.decision_stack.iter() {
            println!("{:?}", l);
        }

        assert_eq!(model.decision_stack, vec![
            (0, 1, Some(Rc::clone(&model.clauses[0]))),
            (0, -2, Some(Rc::new(vec![2]))),
        ])
    }

    #[test]
    fn test_backjumping() {

        let mut model = Model::new(vec![
            vec![-1, -2, -3],
            vec![-1, -2, -4, 5],
            vec![-1, -2, -4, -5],
        ]);

        model.decide(1, &1, None);
        model.decide(2, &2, None);
        model.decide(2, &-3, Some(Rc::clone(&model.clauses[0])));
        model.decide(3, &4, None);
        model.decide(3, &5, Some(Rc::clone(&model.clauses[1])));

        println!("initial decision stack:");
        for l in model.decision_stack.iter() {
            println!("{:?}", l);
        }

        model.backjump(&4, &Rc::new(vec![-1, -2, -4]));

        println!("final decision stack:");
        for l in model.decision_stack.iter() {
            println!("{:?}", l);
        }

        assert_eq!(model.decision_stack, vec![
            (1, 1, None),
            (2, 2, None),
            (2, -3, Some(Rc::clone(&model.clauses[0]))),
            (2, -4, Some(Rc::new(vec![-1, -2, -4]))),
        ])
    }
}
