use std::fmt;
use std::collections::{HashMap, HashSet, VecDeque};

use either::{Either, Right, Left};

use crate::model::{Var, Lit, Clause, ConflictClause, UnitClauses, VarState, Assignment};

enum LitState { Satisfied, Unsatisfied, Unknown, }

#[derive(Debug)]
pub struct WatchedLiterals<'a> {
    attached_clauses: HashMap<Var, (HashSet<&'a Clause>, HashSet<&'a Clause>)>,
    sentinels: HashMap<&'a Clause, (Lit, Lit)>,
    singleton_clauses: Vec<&'a Clause>,
}

impl<'a> WatchedLiterals<'a> {
    pub fn new(clauses: &'a Vec<Clause>, variables: &HashSet<Var>) -> WatchedLiterals<'a> {
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

    fn get_clauses(
        &self,
        lit: &Lit
    ) -> &HashSet<&'a Clause> {
        let (pos, neg) =
            self.attached_clauses.get(&(lit.abs() as Var)).unwrap();
        if lit.is_positive() { pos } else { neg }
    }

    fn get_mut_clauses(
        &mut self,
        lit: &Lit
    ) -> &mut HashSet<&'a Clause> {
        let (pos, neg) =
            self.attached_clauses.get_mut(&(lit.abs() as Var)).unwrap();
        if lit.is_positive() { pos } else { neg }
    }

    fn get_other_watched_sentinel(
        &self,
        clause: &Clause,
        lit: &Lit
    ) -> Lit {
        let wl = self.sentinels.get(clause).unwrap();
        if wl.0 == *lit { wl.1 } else if wl.1 == *lit { wl.0 } else {
            panic!("Asked for other sentinel but the literal is not in the clause");
        }
    }

    fn lit_state(
        lit: &Lit,
        assignment: &Assignment
    ) -> LitState {
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
        assignment: &Assignment,
    ) -> Option<Lit> {
        clause.iter()
            .filter(|&l| (*l != *wl1) & (*l != *wl2))
            .find(|&l| match Self::lit_state(l, &assignment) {
                LitState::Satisfied | LitState::Unknown => true,
                LitState::Unsatisfied => false,
            })
            .map(Lit::clone)
    }

    pub fn replace(
        &mut self,
        clause: &'a Clause,
        old: &Lit,
        new: &Lit,
        other: &Lit,
    ) {
        let s = self.sentinels.get_mut(clause).unwrap();
        *s = (*new, *other);
        assert_eq!(self.get_mut_clauses(old).remove(clause), true);
        assert_eq!(self.get_mut_clauses(new).insert(clause), true);
    }

    pub fn decision(
        &mut self,
        lit: &Lit,
        assignment: &Assignment
    ) -> Either <ConflictClause, UnitClauses<'a>> {

        for &c in self.singleton_clauses.iter() {
            if -lit == c[0] {
                return Left(c.clone());
            }
        }

        /* for every clause where -lit is a watched literal
         * if the other watched literal of the clause is not satisfied (unsatisfied or not assigned)
         * search for a new not unsatisfied literal (satisfied or not assigned) in the clause
         * if you find it, replace it with -lit as a watched literal
         * if you don't find it, match the other literal:
         * if the other literal is undefined, then we have a new unit clause, and
         * the unit literal is the other literal
         * if the other literal is false, then we have a conflict clause
         */

        let mut unit_clauses: UnitClauses = UnitClauses::new();
        let neg_clauses: &HashSet<&Clause> = self.get_clauses(&-lit);

        let mut replacements: Vec<(&Clause, Lit, Lit, Lit)> = Vec::new();

        // while let Some(clause) = self.get_any_clause(-lit) {
        for &clause in neg_clauses.iter() {
            let other_lit = self.get_other_watched_sentinel(&clause, &-lit);
            match Self::lit_state(&other_lit, &assignment) {
                LitState::Satisfied => { continue; },
                LitState::Unsatisfied | LitState::Unknown => {
                    match Self::search_not_sat(&clause, &-lit, &other_lit, &assignment) {
                        Some(newlit) => {
                            replacements.push((clause, -*lit, newlit, other_lit));
                        },
                        None => {
                            match Self::lit_state(&other_lit, &assignment) {
                                LitState::Unknown => {
                                    unit_clauses.push_back((clause, other_lit));
                                },
                                LitState::Unsatisfied => { return Left(clause.clone()); }
                                LitState::Satisfied => { panic!("cannot be here"); }
                            }
                        }
                    }
                }
            }
        }

        for (c, old, new, other) in replacements {
            self.replace(c, &old, &new, &other);
        }

        Right(unit_clauses)
    }

    // pub fn learn_clause(
    //     &mut self,
    //     clause: Clause,
    //     lit: &Lit
    // ) {
    //     if clause.len() == 1{
    //         self.singleton_clauses.push(clause);
    //     } else {
    //         // search for sentinels to watch: a learnt clause is surely conflict, and will
    //         // become satisfied in the next step (that is a backjump), so it's important to
    //         // watch the literal that is going to become true (the assertion literal), while
    //         // the choice of the other literal is not important because they all are unsatisfied.
    //         let other_wl = if clause[0] == *lit { clause[1] } else { clause[0] };

    //         // put sentinels in sentinels[clause]
    //         self.sentinels.insert(&clause, (*lit, other_wl));

    //         // put clause in attached_clause[sent.] for each sent. in sentinels
    //         for l in [*lit, other_wl] {
    //             let (pos, neg) =
    //                 self.attached_clauses.get_mut(&(l.abs() as Var)).unwrap();
    //             if l > 0 {
    //                 pos.insert(clause);
    //             } else {
    //                 neg.insert(clause);
    //             }
    //         }
    //     }

    // }

}

impl<'a> fmt::Display for WatchedLiterals<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // singleton clauses
        writeln!(f, "* singleton clauses: {:?}", self.singleton_clauses)?;

        // sentinels
        writeln!(f, "* sentinels:")?;
        for (c, (l1, l2)) in self.sentinels.iter() {
            writeln!(f, "  {c:?}: ({l1}, {l2})")?;
        }

        // attached clauses
        writeln!(f, "* attached clauses:")?;
        for (v, (pos, neg)) in self.attached_clauses.iter() {
            writeln!(f, "  {v}: {pos:?} & {neg:?} ")?;
        }

        write!(f, "")
    }
}
