use std::collections::{HashSet, HashMap, VecDeque};

use either::{Left, Right};

use crate::watched_literals::WatchedLiterals;
use crate::cvsids::CVSIDS;

pub type Var = u32;
pub type Lit = i32;
pub type Clause = Vec<Lit>;

pub enum VarState { Positive, Negative, Undefined, }

pub type ConflictClause = Clause;
pub type UnitClauses<'a> = VecDeque<(&'a Clause, Lit)>;

enum SolverState<'a> { Propagating(UnitClauses<'a>), Resolving(ConflictClause) }

pub struct Model<'a> {
    assignment: HashMap<Var, VarState>,
    decision_stack: Vec<(i32, Lit, Option<&'a Clause>)>,
}

impl<'a> Model<'a> {
    fn decide(&mut self, dl: i32, lit: &Lit, justification: Option<&'a Clause>) {
        // update decision stack
        self.decision_stack.push((dl, *lit, justification));

        // update assignments
        let val = self.assignment.get_mut(&(lit.abs() as Var)).unwrap();
        *val = if lit.is_positive() { VarState::Positive } else { VarState::Negative };
    }

    fn resolution_step(&self, left: &Clause, right: &Clause) -> Clause {
        let mut newclause = Clause::new();
        for l in left {
            if !right.contains(&-l) { newclause.push(*l); }
        }
        for r in right {
            if !newclause.contains(&-r) { newclause.push(*r); }
        }
        newclause
    }

    fn revert(&mut self, lit: &Lit) {
        let val = self.assignment.get_mut(&(lit.abs() as Var)).unwrap();
        *val = VarState::Undefined;
    }

    fn get_assertion_lit(&mut self, clause: &Clause, dl: &i32) -> Option<Lit> {
        let last_level_lits: Vec<&Lit> = self.decision_stack.iter()
            .filter(|(lev, lit, _)| *lev == *dl && clause.contains(lit))
            .map(|(_, lit, _)| lit)
            .collect();

        match last_level_lits.len() {
            0 => { panic!("No literal found in last level while checking for assertion clause"); }
            1 => Some( **last_level_lits.first().unwrap() ),
            _ => None,
        }
    }

    pub fn solve(&mut self, clauses: &'a mut Vec<Clause>) -> bool {
        let variables: HashSet<Var> = clauses.iter()
            .flatten()
            .map(|l| l.abs() as u32)
            .collect();
        self.assignment = variables.iter()
            .map(|&v| (v, VarState::Undefined))
            .collect();
        self.decision_stack = Vec::new();
        let mut watched_literals = WatchedLiterals::new(&clauses, &variables);
        let mut cvsids = CVSIDS::new(&variables);

        if !self.decision_stack.is_empty() {
            panic!("Called solve on non empty decision stack");
        }

        let mut unit_clauses: VecDeque<(Lit, &Clause)> = clauses.iter()
            .filter(|&c| c.len() == 1)
            .map(|c| (c[0], c))
            .collect();

        let mut dl = 0;

        // initial unit propagation
        while let Some((lit, clause)) = unit_clauses.pop_front() {
            self.decide(dl, &lit, Some(clause));

            match watched_literals.decision(&lit, &self.assignment) {
                Left(_conflict) => { return false; },
                Right(units) => {
                    for (uc, l) in units {
                        unit_clauses.push_back((l, uc))
                    }
                }
            }
        }

        while !self.decision_stack.len() == self.assignment.len() {
            let picked_lit = cvsids.pick_literal();

            dl += 1;
            self.decide(dl, &picked_lit, None);

            let mut solver_state =
                match watched_literals.decision(&picked_lit, &self.assignment) {
                    Left(conflict) => SolverState::Resolving(conflict),
                    Right(units) => SolverState::Propagating(units)
            };


            loop {
                match &mut solver_state {
                    SolverState::Resolving(conflict) => {

                        if dl == 0 {
                            return false;
                        }

                        if let Some(assertion_lit) = self.get_assertion_lit(conflict, &dl) {
                            let confl = conflict.clone();

                            // bump
                            confl.iter()
                                .for_each(|l| cvsids.bump(&(l.abs() as Var)));

                            // learn (1)
                            watched_literals.learn_clause(&confl, &assertion_lit);

                            // backjump
                            let non_assert_lits: HashSet<&Lit> = confl.iter()
                                .filter(|&l| *l != assertion_lit)
                                .collect();

                            while let Some((level, lit, justification)) =
                                self.decision_stack.pop() {
                                if non_assert_lits.contains(&-lit) {
                                    self.decision_stack.push((level, -lit, justification));
                                    break;
                                } else {
                                    self.revert(&lit);
                                    cvsids.revert_variable(&(lit.abs() as Var));
                                }
                            }

                            if let Some((level, _, _)) =
                                self.decision_stack.get(self.decision_stack.len() - 1) {
                                dl = *level;
                            } else {
                                dl = 0;
                            }

                            self.decide(dl, &assertion_lit, Some(&confl));
                            match watched_literals.decision(&assertion_lit, &self.assignment) {
                                Left(confl) => {
                                    solver_state = SolverState::Resolving(confl);
                                },
                                Right(units) => {
                                    solver_state = SolverState::Propagating(units);
                                }
                            }

                            // learn (2)
                            clauses.push(confl);


                        } else {
                            // resolve
                            let justification = self.decision_stack.iter()
                                .rev()
                                .find(|(_, l, _)| conflict.contains(l))
                                .map(|(_, _, j)| j)
                                .expect("found no justification for conflict during resolution")
                                .expect("resolution found is a decision");

                            *conflict = self.resolution_step(&conflict, &justification);
                        }
                    },
                    SolverState::Propagating(units) => {
                        if let Some((uc, lit)) = units.pop_front() {
                            self.decide(dl, &lit, Some(uc));
                            match &mut watched_literals.decision(&lit, &self.assignment) {
                                Left(conflict) => {
                                    solver_state = SolverState::Resolving(conflict.clone());
                                },
                                Right(new_units) => {
                                    units.append(new_units);
                                }
                            }
                        } else {
                            break;
                        }
                    }
                }
            }
        }
        true
    }

}

