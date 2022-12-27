use std::collections::{HashMap, HashSet};

use either::{Either, Right, Left};

use crate::model::{Var, Lit, Clause, ConflictClause, UnitClauses, VarState};

enum LitState { Satisfied, Unsatisfied, Unknown, }

pub struct WatchedLiterals<'a> {
    pub attached_clauses: HashMap<Var, (HashSet<&'a Clause>, HashSet<&'a Clause>)>,
    pub sentinels: HashMap<&'a Clause, (Lit, Lit)>,
    pub singleton_clauses: Vec<&'a Clause>,
}

fn get_clauses<'a, 'b>(
    attached_clauses: &'a HashMap<Var, (HashSet<&'b Clause>, HashSet<&'b Clause>)>,
    lit: &Lit
) -> &'a HashSet<&'b Clause> {
    let (pos, neg) = attached_clauses.get(&(lit.abs() as Var)).unwrap();
    if lit.is_positive() { pos } else { neg }
}

fn get_other_watched_sentinel(
    sentinels: &HashMap<&Clause, (Lit, Lit)>,
    clause: &Clause,
    lit: &Lit
) -> Lit {
    let wl = sentinels.get(clause).unwrap();
    if wl.0 == *lit { wl.1 } else if wl.1 == *lit { wl.0 } else {
        panic!("Asked for other sentinel but the literal is not in the clause");
    }
}

fn lit_state(lit: &Lit, assignment: &HashMap<Var, VarState>) -> LitState {
    match assignment.get(&(lit.abs() as Var)).unwrap() {
        VarState::Positive => if lit.is_positive() { LitState::Satisfied }
        else { LitState::Unsatisfied },
        VarState::Negative => if lit.is_negative() { LitState::Satisfied }
        else { LitState::Unsatisfied },
        VarState::Undefined => LitState::Unknown,
    }
}

fn search_not_sat(
    clause: &Clause,
    wl1: &Lit,
    wl2: &Lit,
    assignment: &HashMap<Var, VarState>,
) -> Option<Lit> {
    clause.iter()
        .filter(|&l| (*l != *wl1) & (*l != *wl2))
        .find(|&l| match lit_state(l, &assignment) {
            LitState::Satisfied | LitState::Unknown => true,
            LitState::Unsatisfied => false,
        })
        .map(Lit::clone)
}

pub fn decision<'a>(
    singleton_clauses: &Vec<&'a Clause>,
    attached_clauses: &mut HashMap<Var, (HashSet<&'a Clause>, HashSet<&'a Clause>)>,
    sentinels: &mut HashMap<&'a Clause, (Lit, Lit)>,
    lit: &Lit,
    assignment: &HashMap<Var, VarState>
) -> Either<ConflictClause, UnitClauses<'a>> {
    for &c in singleton_clauses.iter() {
        if *lit == c[0] {
            return Left((*c).clone());
        }
    }

    // for every clause where -lit is a watched literal
    // if the other watched literal of the clause is
    //  not satisfied (unsatisfied or not assigned)
    // search for a new not unsatisfied literal (satisfied or not assigned)
    //   in the clause
    // if you find it, replace it with -lit as a watched literal
    // if you don't find it, match the other literal:
    // if the other literal is undefined, then we have a new unit clause, and
    //  the unit literal is the other literal
    // if the other literal is false, then we have a conflict clause

    let mut unit_clauses: UnitClauses = UnitClauses::new();
    let neg_clauses = get_clauses(&attached_clauses, lit);

    // while let Some(clause) = self.get_any_clause(-lit) {
    for &clause in neg_clauses.iter() {
        let other_lit = get_other_watched_sentinel(&sentinels, &clause, &-lit);
        match lit_state(&other_lit, &assignment) {
            LitState::Satisfied => { continue; },
            LitState::Unsatisfied | LitState::Unknown => {
                match search_not_sat(&clause, &-lit, &other_lit, &assignment) {
                    Some(newlit) => {
                        // replace watched literals
                        sentinels.insert(clause, (newlit, other_lit));

                        let (pos, neg) =
                            attached_clauses.get_mut(&(lit.abs() as Var)).unwrap();
                        if lit.is_positive() {
                            pos.remove(clause);
                        } else {
                            neg.remove(clause);
                        }

                        let (pos2, neg2) =
                            attached_clauses.get_mut(&(newlit.abs() as Var)).unwrap();
                        if newlit.is_positive() {
                            pos2.insert(clause);
                        } else {
                            neg2.insert(clause);
                        }

                    },
                    None => {
                        match lit_state(&other_lit, &assignment) {
                            LitState::Unknown => {
                                unit_clauses.push_back((&clause, other_lit));
                            },
                            LitState::Unsatisfied => {
                                return Left(clause.clone());
                            }
                            LitState::Satisfied => {
                                panic!("cannot be here");
                            }
                        }
                    },
                }
            }
        }
    }
    Right(unit_clauses)
}

impl<'a> WatchedLiterals<'a> {
    pub fn new(clauses: &Vec<Clause>, variables: &HashSet<Var>) -> WatchedLiterals<'a> {
        let mut wl = WatchedLiterals {
            attached_clauses: variables.iter()
                .map(|&v| (v, (HashSet::new(), HashSet::new())))
                .collect(),
            sentinels: clauses.iter()
                .filter(|&c| c.len() > 1)
                .map(|c| (c, (c[0], c[1])))
                .collect(),
            singleton_clauses: clauses.iter()
                .filter(|c| c.len() == 1)
                .collect(),
        };

        for (&clause, (l1, l2)) in wl.sentinels.iter() {
            for l in [l1, l2] {
                let (pos, neg) =
                    wl.attached_clauses.get_mut(&(l.abs() as u32))
                        .expect("While creating watched literals");

                if *l > 0 {
                    pos.insert(clause);
                } else {
                    neg.insert(clause);
                }

            }
        }
        wl
    }

    pub fn learn_clause(&mut self, clause: &'a Clause, lit: &Lit) {
        if clause.len() == 1{
            self.singleton_clauses.push(clause);
        } else {
            // search for sentinels to watch: a learnt clause is surely conflict, and will
            // become satisfied in the next step (that is a backjump), so it's important to
            // watch the literal that is going to become true (the assertion literal), while
            // the choice of the other literal is not important because they all are unsatisfied.
            let other_wl = if clause[0] == *lit { clause[1] } else { clause[0] };

            // put sentinels in sentinels[clause]
            self.sentinels.insert(&clause, (*lit, other_wl));

            // put clause in attached_clause[sent.] for each sent. in sentinels
            for l in [*lit, other_wl] {
                let (pos, neg) =
                    self.attached_clauses.get_mut(&(l.abs() as Var)).unwrap();
                if l > 0 {
                    pos.insert(clause);
                } else {
                    neg.insert(clause);
                }
            }

        }

    }

}
