use std::collections::{HashMap, VecDeque};
use std::rc::Rc;
use crate::types::*;

// use log::{debug};
// use either::*;
// use crate::watched_literals::WatchedLiterals;
// use crate::cvsids::CVSIDS;

/*
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
*/

pub struct SolverStats {
    conflicts: i32,
}

// #[derive(Debug)]
// pub struct Assignment {
//     lit     : Lit,
//     reason  : Option<Rc<Clause>>
// }

pub struct Solver {
    clauses : Vec<Rc<Clause>>,
    learnt  : Vec<Rc<Clause>>,
    trail   : Vec<Lit>,
    lim     : Vec<usize>,
    model   : HashMap<Var, Sign>,
    reason  : HashMap<Var, Rc<Clause>>,
    level   : HashMap<Var, usize>,
    propq   : VecDeque<Lit>,
    watches : HashMap<Lit, Vec<Rc<Clause>>>,
    attach  : HashMap<Rc<Clause>, (Lit, Lit)>,
    // proof   : Vec<(ClauseRef, ClauseRef, Clause)>,
    stats   : SolverStats,
}

impl Solver {
    pub fn new() -> Solver {
        Solver {
            clauses: Vec::new(),
            learnt: Vec::new(),
            trail: Vec::new(),
            lim: Vec::new(),
            reason: HashMap::new(),
            level: HashMap::new(),
            propq: VecDeque::new(),
            watches: HashMap::new(),
            attach: HashMap::new(),
            model: HashMap::new(),
            // proof: Vec::new(),
            stats: SolverStats { conflicts: 0 }
        }
    }

    pub fn add_clause(&mut self, lits: Vec<Lit>, learnt: bool) -> bool {
        for lit in lits.iter() {
            if !self.model.contains_key(&lit.var()) {
                self.model.insert(lit.var(), Sign::Undef);
            }

            for l in [lit, &lit.neg()] {
                if !self.watches.contains_key(l) {
                    self.watches.insert(*l, Vec::new());
                }
            }
        }

        match lits.len() {
            0 => return false,
            1 => {
                let lit = lits[0];
                let clause = Rc::new(Clause::from_lits(lits));
                if learnt {
                    self.learnt.push(Rc::clone(&clause));
                } else {
                    self.clauses.push(Rc::clone(&clause));
                }
                self.enqueue(lit, Some(clause))
            },
            _ => {
                let l0 = lits[0];
                let l1 = lits[1];
                let clause = Rc::new(Clause::from_lits(lits));
                for l in [l0, l1] {
                    if let Some(clauses) = self.watches.get_mut(&l) {
                        clauses.push(Rc::clone(&clause));
                    } else {
                        panic!("");
                        // self.watches.insert(l, vec![Rc::clone(&clause)]);
                    }
                }
                self.attach.insert(Rc::clone(&clause), (l0, l1));
                if learnt {
                    self.learnt.push(clause);
                } else {
                    self.clauses.push(clause);
                }
                true
            }
        }
    }

    fn state(&self, lit: Lit) -> State {
        match self.model.get(&lit.var()) {
            Some(Sign::Undef) => State::Undef,
            Some(s) => if *s == lit.sign() { State::Sat } else { State::Unsat },
            None => panic!("unknown variable"),
        }
    }

    fn enqueue(&mut self, lit: Lit, reason: Option<Rc<Clause>>) -> bool {
        match self.state(lit) {
            State::Unsat => false,
            State::Sat => true,
            State::Undef => {
                self.model.insert(lit.var(), lit.sign());
                self.level.insert(lit.var(), self.decision_level());
                self.trail.push(lit);
                if let Some(r) = reason {
                    self.reason.insert(lit.var(), r);
                }
                self.propq.push_front(lit);
                true
            }
        }
    }

    fn decision_level(&self) -> usize {
        self.lim.len()
    }

    fn watch(&self, clause: &Rc<Clause>, idx: usize) -> Lit {
        match idx {
            0 => self.attach.get(clause).expect("clause not found").0,
            1 => self.attach.get(clause).expect("clause not found").1,
            _ => panic!("invalid index for watched literal, can be only 1 or 0")
        }
    }

    fn swap_lits(&mut self, clause: &Rc<Clause>) {
        let (l0, l1) = self.attach.get(clause).unwrap();
        self.attach.insert(Rc::clone(&clause), (*l1, *l0));
    }

    fn set_lit(&mut self, clause: &Rc<Clause>, lit: Lit, idx: usize) {
        let (l0, l1) = self.attach.get(clause).unwrap();
        match idx {
            0 => self.attach.insert(Rc::clone(&clause), (lit, *l1)),
            1 => self.attach.insert(Rc::clone(&clause), (*l0, lit)),
            _ => panic!("invalid index for watched literal, can be only 1 or 0")
        };
    }

    // inserts `clause` in the list of clauses that have `lit` as a watched literal
    fn insert_clause(&mut self, clause: Rc<Clause>, lit: Lit) {
        if let Some(clauses) = self.watches.get_mut(&lit) {
            clauses.push(clause);
        } else {
            panic!("No clauses list found for literal");
        }
    }

    // do propagation based on the value of the given clause,
    // pre-conditions: `lit.neg()` is a watched literal of `clause`,
    // `clause` is not a singleton clause, and `clause` is not in
    // `self.watches[lit.neg()]`.
    fn propagate_clause(&mut self, clause: Rc<Clause>, lit: Lit) -> bool {
        // make sure -lit is not the 0th watched literal
        if self.watch(&clause, 0) == lit.neg() {
            self.swap_lits(&clause);
        }

        // the other literal is satisfied: insert back
        if self.state(self.watch(&clause, 0)) == State::Sat {
            self.insert_clause(clause, lit.neg());
            return true;
        }

        // search for a new literal
        let newlit = clause.lits().iter()
            .filter(|&l| (*l != self.watch(&clause, 0)) & (*l != self.watch(&clause, 1)))
            .find(|&l| self.state(*l) != State::Unsat);

        match newlit {
            Some(l) => {
                // change it with -lit
                self.set_lit(&clause, *l, 1);
                self.insert_clause(Rc::clone(&clause), *l);
                true
            },
            None => {
                // unit or conflict
                self.insert_clause(Rc::clone(&clause), lit.neg()); // insert back
                self.enqueue(self.watch(&clause, 0), Some(clause)) // if there's a conflict, this will
                                                                   // return false
            }
        }
    }

    fn propagate(&mut self) -> Option<Rc<Clause>> {
        while let Some(l) = self.propq.pop_back() {
            let tmp: Vec<Rc<Clause>> = Vec::clone(self.watches.get(&l.neg()).unwrap());
            self.watches.get_mut(&l.neg()).unwrap().clear();
            for clause in tmp {
                if !self.propagate_clause(Rc::clone(&clause), l) {
                    // propagation failed: conflict
                    self.propq.clear();
                    return Some(clause)
                }
            }
        }
        None
    }

    fn calc_reason(&self, confl: &Clause, lit: Option<Lit>) -> Vec<Lit> {
        if let Some(l) = lit {
            confl.lits().iter().filter(|&x| *x != l).map(Lit::clone).collect()
        } else {
            Vec::from(confl.lits())
        }
    }

    fn level(&self, var: Var) -> usize {
        *self.level.get(&var).unwrap()
    }

    fn undo_one(&mut self) {
        let v = self.trail.last().unwrap().var();
        // TODO: remove unwrap
        self.model.insert(v, Sign::Undef);
        self.reason.remove(&v); // .unwrap();
        self.level.remove(&v).unwrap();

        self.trail.pop().unwrap();

        if let Some(lastlim) = self.lim.last() {
            self.lim.pop();
        }
    }

    fn cancel(&mut self) {
        let c = self.trail.len() - self.lim.last().unwrap();
        for _ in [0..c] {
            println!("undoing one");
            self.undo_one();
        }
        // self.lim.pop().unwrap();
    }

    fn cancel_until(&mut self, lev: usize) {
        while self.decision_level() > lev {
            self.cancel();
        }
    }

    // analyze a conflicts and produces a level to backtrack and the literals of an 1-UIP clause
    // post-conditions: the 1-UIP literal is the first literal of the output literals.
    fn analyze(&mut self, confl: Rc<Clause>) -> (usize, Vec<Lit>) {

        let mut seen: HashMap<Var, bool> = self.model.iter()
            .map(|(&k, _)| (k, false))
            .collect();

        let mut confl = Some(confl);
        let mut reason: Vec<Lit>;
        let mut counter = 0;
        let mut lit: Option<Lit> = None;
        let mut out_learn: Vec<Lit> = vec![Lit::from_i32(0)]; // space for 1-UIP literal
        let mut out_blevel: usize = 0;

        loop {
            reason = self.calc_reason(&confl.unwrap(), lit);

            for l in reason.iter() {
                if !seen.get(&l.var()).unwrap() {
                    seen.insert(l.var(), true);
                    if self.level(l.var()) == self.decision_level() {
                        counter += 1;
                    } else if self.level(l.var()) > 0 {
                        out_learn.push(l.neg());
                        out_blevel = out_blevel.max(self.level(l.var()));
                    }
                }
            }

            loop {
                lit = Some(*self.trail.last().unwrap()); // yes, i know
                confl = self.reason.get(&lit.unwrap().var()).map(Rc::clone);
                self.undo_one();

                if *seen.get(&lit.unwrap().var()).unwrap() {
                    break;
                }
            }

            counter -= 1;

            if counter <= 0 {
                break;
            }
        }

        out_learn[0] = lit.unwrap().neg();

        (out_blevel, out_learn)

    }

    fn decide(&mut self, lit: Lit) {
        self.lim.push(self.trail.len());
        if !self.enqueue(lit, None) {
            panic!("conflict right after decision");
        }
    }

    // learns an assertion clause.
    // preconditions: `lits[0]` is the assertion literal and `lits.len()` is not zero
    fn learn(&mut self, lits: Vec<Lit>) {
        let l = lits[0];
        let is_unit: bool = lits.len() > 1;
        self.add_clause(lits, true); // if units, propagates, else pushes it to `self.learnt`
                                     // also, watched literals are the first two of `lits`
        if is_unit {
            let clauseref = self.learnt.last().unwrap();
            self.enqueue(l, Some(Rc::clone(clauseref)));
        }
    }

    fn n_assigns(&self) -> usize {
        self.model.iter().filter(|(&v, &s)| s != Sign::Undef).count()
    }

    fn n_vars(&self) -> usize {
        self.model.len()
    }

    fn choose(&self) -> Lit {
        let v = self.model.iter().find(|(&v, &s)| s == Sign::Undef).map(|(&v, &s)| v).unwrap();
        v.to_lit(Sign::Pos)
    }

    fn search(&mut self) -> bool {
        loop {
            println!("propagating...");
            if let Some(confl) = self.propagate() {
                println!("trail: {:?}", self.trail);
                println!("conflict: {confl:?}");

                if self.decision_level() == 0 {
                    return false;
                }
                let (lev, assert_lits) = self.analyze(confl);

                println!("lev: {}, assert_lits: {:?}", lev, assert_lits);
                println!("trail after analyze: {:?}", self.trail);

                self.cancel_until(lev);
                self.learn(assert_lits);
            } else {
                println!("trail: {:?}", self.trail);
                if self.n_assigns() == self.n_vars() {
                    return true;
                } else {
                    let newlit = self.choose();
                    println!("deciding {newlit:?}");
                    self.decide(newlit);
                }
            }
        }
    }

    /*
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
            c'onflicts: self.conflicts,
        }
    }

    fn revert(&mut self, lit: &Lit) {
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

    pub fn solve(mut self) -> (Either<ResolutionProof, Assignment>, Stats) {
        let mut max_conflicts: i32 = 100;
        let mut status: Option<bool> = None;

        while status.is_none() {
            status = self.search(max_conflicts);
            max_conflicts = ((max_conflicts as f32) * 1.5) as i32;
            self = self.reset();
            println!("too many conflict, resetting...")
        }

        (
            match status.unwrap() {
                false => Left(self.proof),
                true => Right(self.assignment),
            },
            Stats { conflicts: self.conflicts }
        )
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
                                self.conflicts += 1;
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
                                    self.conflicts += 1;
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
    */
}

#[cfg(test)]
mod test {
    use super::*;

    fn make_clause(lits: Vec<i32>) -> Vec<Lit> {
        lits.into_iter().map(Lit::from_i32).collect()
    }

    #[test]
    fn test_add_empty_clause() {
        let mut solver = Solver::new();
        assert_eq!(solver.add_clause(vec![], false), false)
    }

    #[test]
    fn test_add_singleton_clause() {
        let mut solver = Solver::new();
        solver.add_clause(vec![Lit::from_i32(1)], false);
        println!("model: {:?}", solver.model);
        assert_eq!(solver.model, HashMap::from([(Var::from_u32(1), Sign::Pos)]));
    }

    #[test]
    fn test_propagation() {
        let mut solver = Solver::new();
        assert_eq!(solver.add_clause(vec![Lit::from_i32(1), Lit::from_i32(2)], false), true);
        assert_eq!(solver.add_clause(vec![Lit::from_i32(-1)], false), true);
        assert_eq!(solver.propagate(), None);
        assert_eq!(solver.model, HashMap::from([(Var::from_u32(1), Sign::Neg),
                                                (Var::from_u32(2), Sign::Pos)]));
    }

    #[test]
    fn test_conflict_enqueue() {
        let mut solver = Solver::new();
        assert_eq!(solver.add_clause(make_clause(vec![1]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1]), false), false);
    }

    #[test]
    fn test_conflict_propagation() {
        let mut solver = Solver::new();
        assert_eq!(solver.add_clause(make_clause(vec![1, 2]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-2, 1]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1]), false), true);
        assert_eq!(solver.propagate().is_some(), true);
    }

    #[test]
    fn test_analyze() {
        let mut solver = Solver::new();
        assert_eq!(solver.add_clause(make_clause(vec![1, 2]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-2, 1]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1]), false), true);
        let conflict = solver.propagate().unwrap();
        let (lev, assert_clause) = solver.analyze(conflict);
    }

    #[test]
    fn test_calc_reason() {
        let solver = Solver::new();
        let clause = Clause::from_lits(make_clause(vec![1, 2, 3]));
        assert_eq!(solver.calc_reason(&clause, Some(Lit::from_i32(3))), Vec::from([Lit::from_i32(1), Lit::from_i32(2)]));
    }

    #[test]
    fn test_propagate_2() {
        let mut solver = Solver::new();
        assert_eq!(solver.add_clause(make_clause(vec![1, 2]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![1, -2]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, 2]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, -2]), false), true);
        solver.decide(Lit::from_i32(1));
        println!("pqueue: {:?}", solver.propq);
        let out = solver.propagate();
        println!("out: {:?}", out);
        assert_eq!(out.is_none(), false);
    }

    #[test]
    fn test_analyze_2() {
        let mut solver = Solver::new();
        assert_eq!(solver.add_clause(make_clause(vec![1, 2]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![1, -2]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, 2]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, -2]), false), true);
        solver.decide(Lit::from_i32(1));
        let confl = solver.propagate().unwrap();
        println!("trail: {:?}", solver.trail);
        println!("level: {:?}", solver.level);
        println!("reason: {:?}", solver.reason);
        println!("conflict: {:?}", confl);
        let (lev, ass_clause) = solver.analyze(confl);
        println!("lev: {lev}, clause: {ass_clause:?}");
        assert_eq!(lev, 0);
        assert_eq!(ass_clause, make_clause(vec![-1]))
        // panic!("the disco");
    }

    #[test]
    fn test_cancel() {
        let mut solver = Solver::new();
        assert_eq!(solver.add_clause(make_clause(vec![1, 2, 3, 4, 5]), false), true);
        solver.decide(Lit::from_i32(1));
        solver.decide(Lit::from_i32(2));
        solver.decide(Lit::from_i32(3));
        solver.decide(Lit::from_i32(4));
        solver.cancel_until(0);
        assert_eq!(solver.decision_level(), 0);
    }

    #[test]
    fn test_cancel_2() {
        let mut solver = Solver::new();
        assert_eq!(solver.add_clause(make_clause(vec![1, 2, 3, 4, 5]), false), true);
        solver.decide(Lit::from_i32(1));
        solver.decide(Lit::from_i32(2));
        solver.decide(Lit::from_i32(3));
        solver.decide(Lit::from_i32(4));
        solver.cancel_until(3);
        println!("trail: {:?}", solver.trail);
        assert_eq!(solver.decision_level(), 3);
    }

    #[test]
    fn test_cancel_3() {
        let mut solver = Solver::new();
        assert_eq!(solver.add_clause(make_clause(vec![1, 2, 3, 4, 5]), false), true);
        solver.decide(Lit::from_i32(1));
        solver.decide(Lit::from_i32(2));
        solver.decide(Lit::from_i32(3));
        solver.decide(Lit::from_i32(4));
        assert_eq!(solver.propagate().is_some(), false);
        solver.cancel_until(3);
        println!("trail: {:?}", solver.trail);
        assert_eq!(solver.decision_level(), 3);
    }

    #[test]
    fn test_learn() {
        let mut solver = Solver::new();
        solver.learn(make_clause(vec![-1, -2]));
        assert_eq!(*solver.learnt.last().unwrap(), Rc::new(Clause::from_lits(make_clause(vec![-1, -2]))));
    }

    #[test]
    fn test_undo_level() {
        let mut solver = Solver::new();
        assert_eq!(solver.add_clause(make_clause(vec![1, 2]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![1, -2]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, 2]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, -2]), false), true);
        solver.decide(Lit::from_i32(1));
        let confl = solver.propagate().unwrap();
        // println!("trail: {:?}", solver.trail);
        // println!("level: {:?}", solver.level);
        // println!("reason: {:?}", solver.reason);
        // println!("conflict: {:?}", confl);
        let (lev, ass_clause) = solver.analyze(confl);

        println!("lev: {lev}, clause: {ass_clause:?}");
        println!("trail: {:?}", solver.trail);
        println!("trail_lim: {:?}", solver.lim);
        println!("decision_level: {:?}", solver.decision_level());

        assert_eq!(lev, 0);
        assert_eq!(ass_clause, make_clause(vec![-1]));
        solver.cancel_until(lev);
    }

    #[test]
    fn simple_test_unsat() {
        let mut solver = Solver::new();
        assert_eq!(solver.add_clause(make_clause(vec![1, 2]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![1, -2]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, 2]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, -2]), false), true);
        assert_eq!(solver.search(), false);
    }

    #[test]
    fn simple_test_sat() {
        let mut solver = Solver::new();
        assert_eq!(solver.add_clause(make_clause(vec![-1, 2]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-2, 3]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-3, 4]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-4, 1]), false), true);
        assert_eq!(solver.search(), true);
    }

    /*
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
    */
}
