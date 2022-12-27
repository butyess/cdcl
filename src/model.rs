use std::collections::{HashSet, HashMap, VecDeque};
use std::rc::Rc;

use either::{Left, Right};

use crate::watched_literals::WatchedLiterals;
use crate::cvsids::CVSIDS;

pub type Var = u32;
pub type Lit = i32;
pub type Clause = Vec<Lit>;

#[derive(Debug)]
pub enum VarState { Positive, Negative, Undefined, }

pub type ConflictClause = Clause;
pub type UnitClauses = VecDeque<(Rc<Clause>, Lit)>;

enum SolverState { Propagating(UnitClauses), Resolving(ConflictClause) }

pub type Assignment = HashMap<Var, VarState>;
type DecisionStack = Vec<(i32, Lit, Option<Rc<Clause>>)>;

fn decide(
    decision_stack: &mut DecisionStack,
    assignment: &mut Assignment,
    dl: i32,
    lit: &Lit,
    justification: Option<Rc<Clause>>
) {
    // update decision stack
    decision_stack.push((dl, *lit, justification));

    // update assignments
    let val = assignment.get_mut(&(lit.abs() as Var)).unwrap();
    *val = if lit.is_positive() { VarState::Positive } else { VarState::Negative };
}

// fn resolution_step(left: &Clause, right: &Clause) -> Clause {
//     let mut newclause = Clause::new();
//     for l in left {
//         if !right.contains(&-l) { newclause.push(*l); }
//     }
//     for r in right {
//         if !newclause.contains(&-r) { newclause.push(*r); }
//     }
//     newclause
// }
//
// fn revert(assignment: &mut Assignment, lit: &Lit) {
//     let val = assignment.get_mut(&(lit.abs() as Var)).unwrap();
//     *val = VarState::Undefined;
// }
//

fn get_assertion_lit(
    decision_stack: &DecisionStack,
    clause: &Clause,
    dl: &i32
) -> Option<Lit> {
    let last_level_lits: Vec<&Lit> = decision_stack.iter()
        .filter(|(lev, lit, _)| *lev == *dl && clause.contains(lit))
        .map(|(_, lit, _)| lit)
        .collect();

    match last_level_lits.len() {
        0 => { panic!("No literal found in last level while checking for assertion clause"); }
        1 => Some( **last_level_lits.first().unwrap() ),
        _ => None,
    }
}

pub fn solve(
    init_clauses: Vec<Clause>
) -> bool {

    let mut clauses: Vec<Rc<Clause>> = init_clauses.into_iter()
        .map(Rc::new)
        .collect();

    let mut variables: HashSet<Var> = HashSet::new();
    clauses.iter()
        .for_each(|c| {
            c.iter() .for_each(|v| { variables.insert(v.abs() as Var); })
        });

    let mut assignment: Assignment = variables.iter()
        .map(|&v| (v, VarState::Undefined))
        .collect();

    let mut decision_stack: DecisionStack = Vec::new();

    let mut cvsids = CVSIDS::new(&variables);
    let mut watched_literals = WatchedLiterals::new(&clauses, &variables);

    let mut unit_clauses: VecDeque<(Lit, Rc<Clause>)> = clauses.iter()
        .filter(|&c| c.len() == 1)
        .map(|c| (c[0], Rc::clone(c)))
        .collect();

    let mut dl = 0;

    // initial unit propagation
    while let Some((lit, clause)) = unit_clauses.pop_front() {
        decide(&mut decision_stack, &mut assignment, dl, &lit, Some(clause));

        match watched_literals.decision(&lit, &assignment) {
            Left(_conflict) => { return false; },
            Right(units) => {
                for (uc, l) in units {
                    unit_clauses.push_back((l, Rc::clone(&uc)))
                }
            }
        }
    }

    while decision_stack.len() < variables.len() {
        let picked_lit = cvsids.pick_literal();
        dl += 1;
        decide(&mut decision_stack, &mut assignment, dl, &picked_lit, None);

        let mut solver_state =
            match watched_literals.decision(&picked_lit, &assignment) {
                Left(conflict) => SolverState::Resolving(conflict),
                Right(units) => SolverState::Propagating(units)
        };

        loop {
            match &mut solver_state {
                SolverState::Resolving(conflict) => {
                    if dl == 0 { return false; }

                    if let Some(assertion_lit) = get_assertion_lit(
                        &decision_stack,
                        conflict,
                        &dl
                    ) {
                        // bump
                        conflict.iter()
                            .for_each(|l| cvsids.bump(&(l.abs() as Var)));

                        // learn (1)
                        // watched_literals.learn_clause(&conflict, &assertion_lit);

                        // // backjump
                        // let non_assert_lits: HashSet<&Lit> = confl.iter()
                        //     .filter(|&l| *l != assertion_lit)
                        //     .collect();

                        // while let Some((level, lit, justification)) =
                        //     decision_stack.pop() {
                        //     if non_assert_lits.contains(&-lit) {
                        //         decision_stack.push((level, -lit, justification));
                        //         break;
                        //     } else {
                        //         revert(&mut assignment, &lit);
                        //         cvsids.revert_variable(&(lit.abs() as Var));
                        //     }
                        // }
                    }
                },
                SolverState::Propagating(units) => { }
            }
        }
    }

    true
}

//         match &mut solver_state {
//             SolverState::Resolving(conflict) => {

//                     if let Some((level, _, _)) =
//                         decision_stack.get(decision_stack.len() - 1) {
//                         dl = *level;
//                     } else {
//                         dl = 0;
//                     }

//                     decide(&mut decision_stack, &mut assignment, dl, &assertion_lit, Some(&confl));
//                     // match watched_literals.decision(&assertion_lit, &assignment) {
//                     match decision(
//                         &watched_literals.singleton_clauses,
//                         &mut watched_literals.attached_clauses,
//                         &mut watched_literals.sentinels,
//                         &assertion_lit,
//                         &assignment,
//                     ) {
//                         Left(confl) => {
//                             solver_state = SolverState::Resolving(confl);
//                         },
//                         Right(units) => {
//                             solver_state = SolverState::Propagating(units);
//                         }
//                     }

//                     // learn (2)
//                     clauses.push(confl);


//                 } else {
//                     // resolve
//                     let justification = decision_stack.iter()
//                         .rev()
//                         .find(|(_, l, _)| conflict.contains(l))
//                         .map(|(_, _, j)| j)
//                         .expect("found no justification for conflict during resolution")
//                         .expect("resolution found is a decision");

//                     *conflict = resolution_step(&conflict, &justification);
//                 }
//             },
//             SolverState::Propagating(units) => {
//                 if let Some((uc, lit)) = units.pop_front() {
//                     decide(&mut decision_stack, &mut assignment, dl, &lit, Some(uc));
//                     // match &mut watched_literals.decision(&lit, &assignment) {
//                     match &mut decision(
//                         &watched_literals.singleton_clauses,
//                         &mut watched_literals.attached_clauses,
//                         &mut watched_literals.sentinels,
//                         &lit,
//                         &assignment,
//                     ) {
//                         Left(conflict) => {
//                             solver_state = SolverState::Resolving(conflict.clone());
//                         },
//                         Right(new_units) => {
//                             units.append(new_units);
//                         }
//                     }
//                 } else {
//                     break;
//                 }
//             }
//         }
