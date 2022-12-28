use std::fmt;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use either::{Either, Right, Left};
use log::info;

use crate::model::{Var, Lit, Clause, ConflictClause, UnitClauses, VarState, Assignment};

enum LitState { Satisfied, Unsatisfied, Unknown, }

#[derive(Debug)]
pub struct WatchedLiterals {
    attached_clauses: HashMap<Var, (HashSet<Rc<Clause>>, HashSet<Rc<Clause>>)>,
    sentinels: HashMap<Rc<Clause>, (Lit, Lit)>,
    singleton_clauses: Vec<Rc<Clause>>,
}

impl WatchedLiterals {
    pub fn new(
        clauses: &Vec<Rc<Clause>>,
        variables: &HashSet<Var>
    ) -> WatchedLiterals {
        let mut wl = WatchedLiterals {
            attached_clauses: variables.iter()
                .map(|&v| (v, (HashSet::new(), HashSet::new())))
                .collect(),
            sentinels: clauses.iter()
                .filter(|&c| c.len() > 1)
                .map(|c| (Rc::clone(c), (c[0], c[1])))
                .collect(),
            singleton_clauses: clauses.iter()
                .filter(|c| c.len() == 1)
                .map(Rc::clone)
                .collect(),
        };

        for (c, (l1, l2)) in wl.sentinels.iter() {
            for l in [l1, l2] {
                let (pos, neg) =
                    wl.attached_clauses.get_mut(&(l.abs() as u32)).unwrap();
                if *l > 0 {
                    pos.insert(Rc::clone(c));
                } else {
                    neg.insert(Rc::clone(c));
                }
            }
        }

        info!("{wl}");

        wl
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

    fn get_clauses(
        &self,
        lit: &Lit
    ) -> &HashSet<Rc<Clause>> {
        let (pos, neg) =
            self.attached_clauses.get(&(lit.abs() as Var)).unwrap();
        if lit.is_positive() { pos } else { neg }
    }

    fn get_mut_clauses(
        &mut self,
        lit: &Lit
    ) -> &mut HashSet<Rc<Clause>> {
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
            info!("clause: {clause:?}, lit: {lit}, wl: {wl:?}");
            info!("lit clauses: {:?}", self.attached_clauses.get(&(lit.abs() as Var)).unwrap());
            info!("wl0 clauses: {:?}", self.attached_clauses.get(&(wl.0.abs() as Var)).unwrap());
            info!("wl1 clauses: {:?}", self.attached_clauses.get(&(wl.1.abs() as Var)).unwrap());
            panic!("Asked for other sentinel but the literal is not in the clause");
        }
    }

    fn replace(
        &mut self,
        clause: Rc<Clause>,
        old: &Lit,
        new: &Lit,
        other: &Lit,
    ) {
        info!("changing {old} with {new} in {clause:?}, where other lit is {other}");
        assert_ne!(old, new);
        assert_ne!(new, other);
        assert_ne!(old, other);
        let s = self.sentinels.get_mut(&clause).unwrap();
        *s = (*new, *other);
        assert_eq!(self.get_mut_clauses(old).remove(&clause), true);
        assert_eq!(self.get_mut_clauses(new).insert(Rc::clone(&clause)), true);

        // info!("old clauses: {:?}", self.attached_clauses.get(&(old.abs() as Var)).unwrap());
        // info!("new clauses: {:?}", self.attached_clauses.get(&(new.abs() as Var)).unwrap());
        // info!("other clauses: {:?}", self.attached_clauses.get(&(other.abs() as Var)).unwrap());
        // info!("clause literals: {:?}", self.sentinels.get(&clause));
    }

    pub fn decision(
        &mut self,
        lit: &Lit,
        assignment: &Assignment
    ) -> Either <ConflictClause, UnitClauses> {

        for c in self.singleton_clauses.iter() {
            if -lit == c[0] {
                return Left((**c).clone());
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
        let neg_clauses: &HashSet<Rc<Clause>> = self.get_clauses(&-lit);

        let mut replacements: Vec<(Rc<Clause>, Lit, Lit, Lit)> = Vec::new();

        // while let Some(clause) = self.get_any_clause(-lit) {
        for clause in neg_clauses.iter() {
            let other_lit = self.get_other_watched_sentinel(clause, &-lit);

            match Self::lit_state(&other_lit, &assignment) {
                LitState::Satisfied => { continue; },
                LitState::Unsatisfied | LitState::Unknown => {
                    match Self::search_not_sat(clause, &-lit, &other_lit, &assignment) {
                        Some(newlit) => {
                            replacements.push((Rc::clone(clause), -*lit, newlit, other_lit));
                        },
                        None => {
                            match Self::lit_state(&other_lit, &assignment) {
                                LitState::Unknown => {
                                    unit_clauses.push_back((Rc::clone(clause), other_lit));
                                },
                                LitState::Unsatisfied => { return Left((**clause).clone()); }
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

    pub fn learn_clause(
        &mut self,
        clause: Rc<Clause>,
        lit: &Lit
    ) {
        info!("learning {clause:?}");
        if clause.len() == 1{
            self.singleton_clauses.push(Rc::clone(&clause));
        } else if self.sentinels.contains_key(&clause) {
            // TODO
        } else {
            // search for sentinels to watch: a learnt clause is surely conflict, and will
            // become satisfied in the next step (that is a backjump), so it's important to
            // watch the literal that is going to become true (the assertion literal), while
            // the choice of the other literal is not important because they all are unsatisfied.
            let other_wl = if clause[0] == *lit { clause[1] } else { clause[0] };

            // put sentinels in sentinels[clause]
            assert_eq!(self.sentinels.insert(Rc::clone(&clause), (*lit, other_wl)), None);

            // put clause in attached_clause[sent.] for each sent. in sentinels
            for l in [*lit, other_wl] {
                let (pos, neg) =
                    self.attached_clauses.get_mut(&(l.abs() as Var)).unwrap();
                if l > 0 {
                    assert_eq!(pos.insert(Rc::clone(&clause)), true);
                } else {
                    assert_eq!(neg.insert(Rc::clone(&clause)), true);
                }
            }
        }

    }

}

impl fmt::Display for WatchedLiterals {
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

#[cfg(test)]
mod test {
    use std::collections::VecDeque;
    use super::*;

    #[test]
    #[should_panic]
    fn test_replace() {
        let clauses: Vec<Rc<Clause>> = vec![
            Rc::new(vec![1, 2, 3]),
        ];
        let variables: HashSet<Var> = HashSet::from([1, 2, 3]);
        let mut wl = WatchedLiterals::new(&clauses, &variables);

        println!("before:\n{wl}");

        wl.replace(Rc::clone(&clauses[0]), &1, &3, &2);

        println!("after:\n{wl}");

    }

    #[test]
    fn test_learn_clause() {
        let clauses: Vec<Rc<Clause>> = vec![
            Rc::new(vec![1, 2, 3]),
        ];
        let variables: HashSet<Var> = HashSet::from([1, 2, 3]);
        let mut wl = WatchedLiterals::new(&clauses, &variables);
        let assignment: Assignment = Assignment::from([
            (1, VarState::Positive),
            (2, VarState::Undefined),
            (3, VarState::Undefined),
        ]);
        wl.learn_clause(Rc::new(vec![-1, -2]), &-1);
        assert_eq!(wl.decision(&1, &assignment), Right(VecDeque::from([
            (Rc::new(vec![-1, -2]), -2),
        ])));
    }

    #[test]
    fn test_decision() {
        let clauses: Vec<Rc<Clause>> = vec![
            Rc::new(vec![-1, 2]),
            Rc::new(vec![-1]),
        ];
        let variables: HashSet<Var> = HashSet::from([1, 2, 3]);
        let mut wl = WatchedLiterals::new(&clauses, &variables);

        let assignment: Assignment = Assignment::from([
            (1, VarState::Positive),
            (2, VarState::Undefined),
            (3, VarState::Undefined),
        ]);

        assert_eq!(wl.decision(&1, &assignment), Left(vec![-1]));
    }

    #[test]
    fn test_decision_2() {
        let clauses: Vec<Rc<Clause>> = vec![
            Rc::new(vec![-1, 3]),
        ];
        let variables: HashSet<Var> = HashSet::from([1, 2, 3]);
        let mut wl = WatchedLiterals::new(&clauses, &variables);

        let assignment: Assignment = Assignment::from([
            (1, VarState::Positive),
            (2, VarState::Undefined),
            (3, VarState::Undefined),
        ]);

        assert_eq!(wl.decision(&1, &assignment), Right(VecDeque::from([
            (Rc::new(vec![-1, 3]), 3),
        ])));
    }

}
