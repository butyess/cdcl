use std::collections::{BTreeMap, VecDeque};
use std::rc::Rc;
use crate::types::*;
use log::{debug, info};

pub struct SolverStats {
    conflicts: i32,
}

pub struct Solver {
    clauses : Vec<Rc<Clause>>,
    learnt  : Vec<Rc<Clause>>,
    trail   : Vec<Lit>,
    lim     : Vec<usize>,
    model   : BTreeMap<Var, Sign>,
    reason  : BTreeMap<Var, Rc<Clause>>,
    level   : BTreeMap<Var, usize>,
    propq   : VecDeque<Lit>,
    watches : BTreeMap<Lit, Vec<Rc<Clause>>>,
    attach  : BTreeMap<Rc<Clause>, (Lit, Lit)>,
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
            reason: BTreeMap::new(),
            level: BTreeMap::new(),
            propq: VecDeque::new(),
            watches: BTreeMap::new(),
            attach: BTreeMap::new(),
            model: BTreeMap::new(),
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
        debug!("enqueuing {lit:?}");
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
            debug!("propagating {l:?}");
            let mut tmp: Vec<Rc<Clause>> = Vec::clone(self.watches.get(&l.neg()).unwrap());
            self.watches.get_mut(&l.neg()).unwrap().clear();


            // for clause in tmp {
            while let Some(clause) = tmp.pop() {
                debug!("watching {clause:?}, literals: {:?}", self.attach.get(&clause));
                if !self.propagate_clause(Rc::clone(&clause), l) {
                    // propagation failed: conflict
                    self.propq.clear();
                    self.watches.get_mut(&l.neg()).unwrap().append(&mut tmp);
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

        debug!("undoing variable {:?}", v);

        // TODO: remove unwrap
        self.model.insert(v, Sign::Undef);
        self.reason.remove(&v); // .unwrap();
        self.level.remove(&v).unwrap();

        self.trail.pop().unwrap();

        if let Some(lastlim) = self.lim.last() {
            if *lastlim == self.trail.len() {
                self.lim.pop();
            }
        }
    }

    fn cancel(&mut self) {
        let c = self.trail.len() - self.lim.last().unwrap();
        for _ in [0..c] {
            debug!("undoing one");
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

        let mut seen: BTreeMap<Var, bool> = self.model.iter()
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

    pub fn search(&mut self) -> bool {
        loop {
            // info!("lits of -10, -18: {:?}", self.attach.get(&Rc::new(Clause::from_lits(vec![
            //                                                                           Lit::from_i32(-10),
            //                                                                           Lit::from_i32(-18),
            // ]))));
            info!("watched of -10: {:?}", self.watches.get(&Lit::from_i32(-10)));

            debug!("prop quque: {:?}", self.propq);
            debug!("propagating...");
            if let Some(confl) = self.propagate() {
                debug!("trail: {:?}", self.trail);
                debug!("conflict: {confl:?}");
                debug!("decision level: {}", self.decision_level());

                if self.decision_level() == 0 {
                    return false;
                }
                let (lev, assert_lits) = self.analyze(confl);

                debug!("lev: {}, assert_lits: {:?}", lev, assert_lits);
                debug!("trail after analyze: {:?}", self.trail);

                self.cancel_until(lev);
                self.learn(assert_lits);

                debug!("trail after learn: {:?}", self.trail);
                debug!("decision level after learning: {}", self.decision_level());
            } else {
                debug!("trail: {:?}", self.trail);
                if self.n_assigns() == self.n_vars() {
                    return true;
                } else {
                    let newlit = self.choose();
                    debug!("deciding {newlit:?}");
                    self.decide(newlit);
                }
            }
        }
    }

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
        debug!("model: {:?}", solver.model);
        assert_eq!(solver.model, BTreeMap::from([(Var::from_u32(1), Sign::Pos)]));
    }

    #[test]
    fn test_propagation() {
        let mut solver = Solver::new();
        assert_eq!(solver.add_clause(vec![Lit::from_i32(1), Lit::from_i32(2)], false), true);
        assert_eq!(solver.add_clause(vec![Lit::from_i32(-1)], false), true);
        assert_eq!(solver.propagate(), None);
        assert_eq!(solver.model, BTreeMap::from([(Var::from_u32(1), Sign::Neg),
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
        debug!("pqueue: {:?}", solver.propq);
        let out = solver.propagate();
        debug!("out: {:?}", out);
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
        debug!("trail: {:?}", solver.trail);
        debug!("level: {:?}", solver.level);
        debug!("reason: {:?}", solver.reason);
        debug!("conflict: {:?}", confl);
        let (lev, ass_clause) = solver.analyze(confl);
        debug!("lev: {lev}, clause: {ass_clause:?}");
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
        debug!("trail: {:?}", solver.trail);
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
        debug!("trail: {:?}", solver.trail);
        assert_eq!(solver.decision_level(), 3);
    }

    #[test]
    fn test_cancel_4() {
        let mut solver = Solver::new();
        assert_eq!(solver.add_clause(make_clause(vec![1, 2, 3, 4, 5]), false), true);
        solver.decide(Lit::from_i32(1));
        solver.decide(Lit::from_i32(2));
        solver.decide(Lit::from_i32(3));
        solver.undo_one();
        solver.undo_one();
        solver.undo_one();
        assert_eq!(solver.decision_level(), 0);
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
        // debug!("trail: {:?}", solver.trail);
        // debug!("level: {:?}", solver.level);
        // debug!("reason: {:?}", solver.reason);
        // debug!("conflict: {:?}", confl);
        let (lev, ass_clause) = solver.analyze(confl);

        debug!("lev: {lev}, clause: {ass_clause:?}");
        debug!("trail: {:?}", solver.trail);
        debug!("trail_lim: {:?}", solver.lim);
        debug!("decision_level: {:?}", solver.decision_level());

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

    #[test]
    fn simple_test_sat_2() {
        let mut solver = Solver::new();
        assert_eq!(solver.add_clause(make_clause(vec![1, 2, -3]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![1, -2, 3]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![1, -2, -3]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, 2, 3]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, 2, -3]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, -2, 3]), false), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, -2, -3]), false), true);

        assert_eq!(solver.propagate().is_some(), false);
        solver.decide(Lit::from_i32(1));
        solver.decide(Lit::from_i32(2));

        let out = solver.propagate();
        assert_eq!(out.is_some(), true);

        let (lev, alits) = solver.analyze(out.unwrap());
        solver.cancel_until(lev);
        debug!("trail: {:?}", solver.trail);
        debug!("decision level: {:?}", solver.decision_level());
        debug!("reason: {:?}", solver.reason);
        debug!("lim: {:?}", solver.lim);
        debug!("level: {:?}", solver.level);

        assert_eq!(solver.decision_level(), 1)

        // assert_eq!(solver.search(), true);
    }
}

