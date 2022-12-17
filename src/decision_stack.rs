use std::rc::Rc;
use std::collections::{HashSet, HashMap};
use std::fmt;

use either::{Either, Left, Right};

use super::model::{Lit, Var, Clause};

#[derive(Debug)]
#[derive(PartialEq)]
enum VarState {
    Positive, Negative, Undefined,
}

#[derive(Debug)]
#[derive(PartialEq)]
enum LitState {
    Satisfied, Unsatisfied, Unknown,
}

#[derive(Debug)]
pub struct DecisionStack {
    pub ds: Vec<Vec<(Lit, Option<Rc<Clause>>)>>,
    sentinels: HashMap<Rc<Clause>, (Lit, Lit)>,
    attached_clauses: HashMap<Var, (HashSet<Rc<Clause>>, HashSet<Rc<Clause>>)>,
    variables_state: HashMap<Var, VarState>,
}

impl fmt::Display for DecisionStack {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for level in self.ds.iter() {
            for decision in level.iter() {
                match &decision.1 {
                    Some(clause) => { write!(f, "{} ({:?}), ", decision.0, *clause)?; },
                    None => { write!(f, "{}", decision.0)?; }
                }
            }

            writeln!(f, "")?;
        }
        write!(f, "")
    }
}

fn lit_to_var(l: &Lit) -> Var {
    Var::try_from(l.abs()).unwrap()
}

fn var_state_from_lit(l: &Lit) -> VarState {
    match l.signum() {
        1 => VarState::Positive,
        -1 => VarState::Negative,
        _ => { panic!("Found literal set to zero") }
    }
}

impl DecisionStack {
    pub fn new(clauses: &Vec<Rc<Clause>>, variables: &HashSet<Var>) -> DecisionStack {
        let variables_state: HashMap<Var, VarState> = variables.iter()
            .map(|x| (x.clone(), VarState::Undefined))
            .collect();
        let sentinels: HashMap<Rc<Clause>, (Lit, Lit)> = clauses.iter()
            .filter(|c| c.len() > 1)
            .map(|c| (Rc::clone(c), (c[0], c[1])))
            .collect();
        let mut attached_clauses: HashMap<Var, (HashSet<Rc<Clause>>, HashSet<Rc<Clause>>)> = variables.iter()
            .map(|v| (v.clone(), (HashSet::new(), HashSet::new())))
            .collect();

        for (clause, (lit1, lit2)) in sentinels.iter() {
            for lit in [lit1, lit2] {
                if let Some((pos, neg)) = attached_clauses.get_mut(&lit_to_var(lit)) {
                    (if *lit > 0 { pos } else { neg }).insert(Rc::clone(clause));
                }
            }
        }

        DecisionStack {
            ds: Vec::new(),
            sentinels: sentinels,
            attached_clauses: attached_clauses,
            variables_state: variables_state,
        }
    }

    pub fn level(&self) -> usize {
        self.ds.len()
    }

    // fn get_any_clause(&self, lit: Lit) -> Option<Rc<Clause>> {
    //     let (pos, neg) = self.attached_clauses.get(&lit_to_var(&lit)).unwrap();
    //     let source = if lit.is_positive() { pos } else { neg };

    //     source.iter().next().and_then(|c| Some(Rc::clone(c)))
    // }

    fn get_clauses(&self, lit: Lit) -> Vec<Rc<Clause>> {
        let (pos, neg) = self.attached_clauses.get(&lit_to_var(&lit)).unwrap();
        if lit.is_positive() {
            pos.iter()
               .map(|c| Rc::clone(c))
               .collect()
        } else {
            neg.iter()
                .map(|c| Rc::clone(c))
                .collect()
        }
    }

    fn get_mut_clauses(&mut self, lit: Lit) -> &mut HashSet<Rc<Clause>> {
        let (pos, neg) = self.attached_clauses.get_mut(&lit_to_var(&lit)).unwrap();
        if lit.is_positive() {
            pos
        } else {
            neg
        }
    }

    fn get_other_watched_sentinel(&self, clause: &Rc<Clause>, lit: Lit) -> Lit {
        let wl = self.sentinels.get(clause).unwrap();
        if wl.0 == lit {
            wl.1
        } else if wl.1 == lit {
            wl.0
        } else {
            panic!("Asked for other sentinel but the literal is not in the clause");
        }
    }

    fn lit_state(&self, lit: Lit) -> LitState {
        match self.variables_state.get(&lit_to_var(&lit)).unwrap() {
            VarState::Positive => if lit.is_positive() { LitState::Satisfied } else { LitState::Unsatisfied },
            VarState::Negative => if lit.is_negative() { LitState::Satisfied } else { LitState::Unsatisfied },
            VarState::Undefined => LitState::Unknown,
        }
    }

    fn search_not_sat(&self, clause: &Rc<Clause>, wl1: Lit, wl2: Lit) -> Option<Lit> {
        clause.iter()
              .map(|l| l.clone())
              .filter(|l| (*l != wl1) & (*l != wl2))
              .find(|l| match self.lit_state(*l) {
                  LitState::Satisfied | LitState::Unknown => true,
                  LitState::Unsatisfied => false,
              })
    }

    fn replace_watched_literal(&mut self, clause: &Rc<Clause>, old: Lit, new: Lit, other: Lit) {
        self.sentinels.insert(Rc::clone(clause), (new, other));
        self.get_mut_clauses(old).remove(clause);
        self.get_mut_clauses(new).insert(Rc::clone(clause));
    }

    fn made_decision(&mut self, lit: Lit) -> Either<Vec<(Rc<Clause>, Lit)>, Rc<Clause>> {
        // for every clause where -lit is a watched literal
            // if the other watched literal of the clause is not satisfied (unsatisfied or not assigned)
                // search for a new not unsatisfied literal (satisfied or not assigned) in the clause
                // if you find it, replace it with -lit as a watched literal
                // if you don't find it, match the other literal:
                    // if the other literal is undefined, then we have a new unit clause, and
                    //  the unit literal is the other literal
                    // if the other literal is false, then we have a conflict clause

        let mut unit_clauses: Vec<(Rc<Clause>, Lit)> = Vec::new();

        let neg_clauses = self.get_clauses(-lit);

        // while let Some(clause) = self.get_any_clause(-lit) {
        for clause in neg_clauses {
            let other_lit = self.get_other_watched_sentinel(&clause, -lit);
            match self.lit_state(other_lit) {
                LitState::Satisfied => { continue; },
                LitState::Unsatisfied | LitState::Unknown => {
                    match self.search_not_sat(&clause, -lit, other_lit) {
                        Some(newlit) => {
                            // self.sentinels.insert(Rc::clone(&clause), (newlit, other_lit));
                            self.replace_watched_literal(&clause, -lit, newlit, other_lit);
                        },
                        None => {
                            match self.lit_state(other_lit) {
                                LitState::Unknown => { unit_clauses.push((Rc::clone(&clause), other_lit)); },
                                LitState::Unsatisfied => { return Right(Rc::clone(&clause)); }
                                LitState::Satisfied => { panic!("cannot be here"); }
                            }
                        },
                    }
                }
            }
        }
        Left(unit_clauses)
    }

    pub fn propagate(&mut self, clause: &Rc<Clause>, lit: Lit) -> Either<Vec<(Rc<Clause>, Lit)>, Rc<Clause>> {
        match self.ds.last_mut() {
            Some(last_level) => { last_level.push((lit, Some(Rc::clone(clause)))); },
            None => { self.ds.push(vec![(lit, Some(Rc::clone(clause)))]); }
        }

        self.variables_state.insert(lit_to_var(&lit), var_state_from_lit(&lit));

        self.made_decision(lit)
    }

    pub fn decide(&mut self, lit: Lit) -> Vec<(Rc<Clause>, Lit)> {
        match self.ds.last_mut() {
            Some(last_level) => { last_level.push((lit, None)); }
            None => { self.ds.push(vec![(lit, None)]); }
        }

        self.variables_state.insert(lit_to_var(&lit), var_state_from_lit(&lit));

        match self.made_decision(lit) {
            Left(units) => { units }
            _ => { panic!("Got a conflict after a decision"); }
        }

    }

    pub fn all_variables_assigned(&self) -> bool {
        self.variables_state.iter()
                            .all(|(_, s)| match *s {
                                VarState::Undefined => false,
                                _ => true,
                            })
    }

    pub fn find_assertion_literal(&self, clause: &Clause) -> Option<Lit> {
        let lastlevel = self.ds.last()
            .expect("No justification because no decision has been made");
        
        let lit_in_last_level: Vec<Lit> = lastlevel.iter()
            .filter(|(l, _)| !clause.contains(l))
            .map(|(l, _)| *l)
            .collect();

        match lit_in_last_level.len() {
            0 => { panic!("No literal found in last level while checking for assertion clause"); }
            1 => Some(*lit_in_last_level.first().unwrap()) ,
            _ => None,
        }
    }

    pub fn find_justification(&self, lit: &Lit) -> Option<&Rc<Clause>> {
        let lastlevel = self.ds.last()
            .expect("No justification because no decision has been made");

        lastlevel.iter()
            .filter(|(l, _c)| *l == *lit)
            .flat_map(|(_l, c)| c)
            .next()
    }

    pub fn learn_clause(&mut self, clause: Rc<Clause>, lit: &Lit) {
        if clause.len() == 1 { return; }

        // search for sentinels to watch: a learnt clause is surely conflict, and will
        // become satisfied in the next step (that is a backjump), so it's important to
        // watch the literal that is going to become true (the assertion literal), while
        // the choice of the other literal is not important because they all are unsatisfied.
        let other_watched_literal = if clause[0] == *lit { clause[1] } else { clause[0] };

        // put sentinels in sentinels[clause]
        self.sentinels.insert(Rc::clone(&clause), (*lit, other_watched_literal));

        // put clause in attached_clause[s] for s in sentinels
        for l in [*lit, other_watched_literal] {
            let (pos, neg) =
                self.attached_clauses.get_mut(&lit_to_var(&l)).unwrap();
            (if l > 0 { pos } else { neg }).insert(Rc::clone(&clause));
        }
    }

    pub fn search_backjump(&mut self, lit: &Lit, clause: &Rc<Clause>) -> Vec<Lit> {
        let non_assert_literals: HashSet<Lit> = clause.iter()
            .filter(|&l| *l != *lit)
            .map(i32::clone)
            .collect();
            
        let mut found_lit: bool = false;
        let mut reverted_literals: Vec<Lit> = Vec::new();

        while let Some(mut last_level) = self.ds.pop() {

            // cannot revert in the last level because its only made of propagations
            if self.ds.len() == 0 {
                assert!(found_lit, "reverting in the last level, but conflict literal still not found");
                self.ds.push(last_level);
                break;
            }

            while let Some((last_lit, c)) = last_level.pop() {
                found_lit = last_lit == *lit;
                if non_assert_literals.contains(&last_lit) {
                    if !found_lit {
                        panic!("Found non assertion literal before the conflict literal in the decision stack");
                    } else {
                        last_level.push((last_lit, c));
                        break;
                    }
                } else {
                    reverted_literals.push(last_lit);
                }
            }

            if last_level.len() > 0 {
                self.ds.push(last_level);
                break;
            }
        }

        reverted_literals

    }

}
