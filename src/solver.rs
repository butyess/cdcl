// TODO:
// - restart (DONE)
// - proof or model (DONE)
// - cvsids (DONE)
// - command line (DONE)
// - forget (DONE)
// - subsumption
// - implement forget in another module (WILL NOT)
// - remove the field `learnt` in add_clause (DONE)
// - remove todo list

use std::collections::{HashMap, VecDeque, HashSet};
use std::rc::Rc;
use crate::types::*;
use crate::varorder::{SignPolicy, VarOrder};

pub struct SolverStats {
    pub conflicts: usize,
    pub restarts: usize,
    pub decisions: usize,
    pub propagations: usize,
}

pub struct SolverOptions {
    pub init_max_conflicts: usize,
    pub max_conflicts_multiplier: f32,
    pub max_learnts_multiplier: f32,
    pub save_proof: bool,
    pub debug: bool,
}

impl Default for SolverOptions {
    fn default() -> SolverOptions {
        SolverOptions {
            init_max_conflicts: 100,
            max_conflicts_multiplier: 1.5f32,
            max_learnts_multiplier: 1.1f32,
            save_proof: true,
            debug: false,
        }
    }
}

pub struct Solver {
    clauses      : Vec<Rc<Clause>>,
    learnt       : HashSet<Rc<Clause>>,
    trail        : Vec<Lit>,
    lim          : Vec<usize>,
    model        : HashMap<Var, Sign>,
    reason       : HashMap<Var, Rc<Clause>>,
    level        : HashMap<Var, usize>,
    propq        : VecDeque<Lit>,
    watches      : HashMap<Lit, Vec<Rc<Clause>>>,
    attach       : HashMap<Rc<Clause>, (Lit, Lit)>,
    proof        : Vec<String>,
    order        : VarOrder,
    cla_activity : HashMap<Rc<Clause>, f64>,
    cla_inc      : f64,
    cla_decay    : f64,
    stats        : SolverStats,
    options      : SolverOptions,
}

impl Solver {
    pub fn new(options: SolverOptions) -> Solver {
        Solver {
            clauses: Vec::new(),
            learnt: HashSet::new(),
            trail: Vec::new(),
            lim: Vec::new(),
            reason: HashMap::new(),
            level: HashMap::new(),
            propq: VecDeque::new(),
            watches: HashMap::new(),
            attach: HashMap::new(),
            model: HashMap::new(),
            proof: Vec::new(),
            order: VarOrder::new(0.95),
            cla_activity: HashMap::new(),
            cla_inc: 1f64,
            cla_decay: 0.999f64,
            stats: SolverStats { conflicts: 0, restarts: 0, decisions: 0, propagations: 0 },
            options,
        }
    }

    pub fn get_stats(&self) -> &SolverStats {
        &self.stats
    }

    pub fn set_pick_policy(&mut self, policy: SignPolicy) {
        self.order.set_policy(policy);
    }

    pub fn set_var_decay(&mut self, decay: f64) {
        self.order.set_decay(decay);
    }

    pub fn add_clause(&mut self, lits: Vec<Lit>) -> bool {
        for lit in lits.iter() {
            if !self.model.contains_key(&lit.var()) {
                self.model.insert(lit.var(), Sign::Undef);
            }

            for l in [lit, &lit.neg()] {
                if !self.watches.contains_key(l) {
                    self.watches.insert(*l, Vec::new());
                }
            }

            self.order.new_var(lit.var());
        }

        let clause: Rc<Clause> = Rc::new(Clause::from_lits(lits));
        match clause.lits().len() {
            0 => return false,
            1 => {
                let lit = clause.lits()[0];
                self.clauses.push(Rc::clone(&clause));
                self.enqueue(lit, Some(clause))
            },
            _ => {
                let (l0, l1) = (clause.lits()[0], clause.lits()[1]);
                if !self.attach.contains_key(&clause) {
                    self.attach.insert(Rc::clone(&clause), (l0, l1));
                    for l in [l0, l1] {
                        self.watches.get_mut(&l)
                            .expect("No watches for literal when adding clause")
                            .push(Rc::clone(&clause));
                    }
                    self.clauses.push(Rc::clone(&clause));
                }
                true
            }
        }
    }

    // pre-conditions: lits.len() > 0
    pub fn learn_clause(&mut self, lits: Vec<Lit>) -> Rc<Clause> {
        let clause: Rc<Clause> = Rc::new(Clause::from_lits(lits));
        if clause.lits().len() > 1 {
            let (l0, l1) = (clause.lits()[0], clause.lits()[1]);
            if !self.attach.contains_key(&clause) {
                self.attach.insert(Rc::clone(&clause), (l0, l1));
                for l in [l0, l1] {
                    self.watches.get_mut(&l)
                        .expect("No watches for literal when learning clause")
                        .push(Rc::clone(&clause));
                }
            }
        }
        self.cla_activity.insert(Rc::clone(&clause), 0f64);
        self.bump_clause(Rc::clone(&clause));
        self.learnt.insert(Rc::clone(&clause));
        clause
    }

    fn state(&self, lit: Lit) -> State {
        match self.model.get(&lit.var()) {
            Some(Sign::Undef) => State::Undef,
            Some(s) => if *s == lit.sign() { State::Sat } else { State::Unsat },
            None => panic!("unknown variable"),
        }
    }

    fn enqueue(&mut self, lit: Lit, reason: Option<Rc<Clause>>) -> bool {
        self.stats.propagations += 1;
        match self.state(lit) {
            State::Unsat => false,
            State::Sat => true,
            State::Undef => {
                self.model.insert(lit.var(), lit.sign());
                self.level.insert(lit.var(), self.decision_level());
                self.trail.push(lit);
                self.order.selected(lit.var());
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
            let mut tmp: Vec<Rc<Clause>> = Vec::clone(self.watches.get(&l.neg()).unwrap());
            self.watches.get_mut(&l.neg()).unwrap().clear();

            // for clause in tmp {
            while let Some(clause) = tmp.pop() {
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

        // TODO: remove unwrap
        self.model.insert(v, Sign::Undef);
        self.reason.remove(&v); // .unwrap();
        self.level.remove(&v).unwrap();
        self.order.undo(v);

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
            let c: Rc<Clause> = confl.unwrap(); // minisat invariant: confl != None
            reason = self.calc_reason(&c, lit);
            self.bump_clause(Rc::clone(&c));
            for l in reason.iter() {
                if !seen.get(&l.var()).unwrap() {
                    seen.insert(l.var(), true);
                    if self.level(l.var()) == self.decision_level() {
                        counter += 1;
                    } else if self.level(l.var()) > 0 {
                        out_learn.push(*l);
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
        let clause: Rc<Clause> = self.learn_clause(lits);
        assert_eq!(true, self.enqueue(clause.lits()[0], Some(clause))); // always true on a learned clause

        // let is_unit: bool = lits.len() == 1;
        // if is_unit {
        //     self.learn_clause(lits);
        // } else {
        //     let l0 = lits[0];
        //     let l1 = lits[1];
        //     let clauseref = Rc::new(Clause::from_lits(lits));
        //     self.add_nonunit_clause(Rc::clone(&clauseref), l0, l1, true);
        //     self.enqueue(l0, Some(clauseref));
        // }
    }

    fn n_assigns(&self) -> usize {
        self.model.iter().filter(|(_, &s)| s != Sign::Undef).count()
    }

    fn n_vars(&self) -> usize {
        self.model.len()
    }

    fn choose(&mut self) -> Lit {
        // let v = self.model.iter().find(|(&v, &s)| s == Sign::Undef).map(|(&v, &s)| v).unwrap();
        // v.to_lit(Sign::Neg)
        self.order.pick()
    }

    fn decay_clauses(&mut self) {
        self.cla_inc *= 1f64 / self.cla_decay;
    }

    fn bump_clause(&mut self, clause: Rc<Clause>) {
        if let Some(val) = self.cla_activity.get_mut(&clause) {
            *val += self.cla_inc;
            if *val > 1e100 {
                self.activity_rescale();
            }
        }
    }

    fn activity_rescale(&mut self) {
        for val in self.cla_activity.values_mut() {
            *val = *val * 1e-100;
        }
        self.cla_inc *= 1e-100;
    }

    fn locked(&self, clause: &Rc<Clause>) -> bool {
        let (l0, l1) = self.attach.get(clause).unwrap();
        for l in [l0, l1] {
            if let Some(cl) = self.reason.get(&l.var()) {
                if cl == clause {
                    return true;
                }
            }
        }
        false
    }

    fn forget(&mut self) {
        let lim: f64 = self.cla_inc / (self.learnt.len() as f64);

        let mut activitysorted: Vec<Rc<Clause>> = self.learnt.iter().map(Rc::clone).collect();
        activitysorted.sort_unstable_by(|a, b| {
            let av = self.cla_activity.get(a).unwrap();
            let bv = self.cla_activity.get(b).unwrap();
            av.partial_cmp(bv).unwrap()
        });

        for i in 0..(activitysorted.len()/2) {
            let clause = activitysorted.get(i).unwrap();
            if !clause.is_unit() && !self.locked(clause) {
                self.remove_clause(Rc::clone(clause));
            }
        }

        let toremove: Vec<Rc<Clause>> = self.learnt.iter().filter(|&c| {
            !(c.is_unit() || self.locked(c) || self.cla_activity.get(c).unwrap().ge(&lim))
        }).map(Rc::clone).collect();

        for c in toremove {
            self.remove_clause(c);
        }
    }

    fn remove_clause(&mut self, clause: Rc<Clause>) {
        assert_eq!(true, self.learnt.remove(&clause));
        let (_, (l0, l1)) = self.attach.remove_entry(&clause).unwrap();

        let l0w = self.watches.get_mut(&l0).unwrap();
        l0w.remove(l0w.iter().position(|x| *x == clause).unwrap());

        let l1w = self.watches.get_mut(&l1).unwrap();
        l1w.remove(l1w.iter().position(|x| *x == clause).unwrap());

        self.cla_activity.remove(&clause);
    }

    fn search(&mut self, max_conflicts_base: usize, max_learnts: usize) -> Option<bool> {
        let mut counter: usize = 0;
        let max_conflicts = max_conflicts_base + self.stats.conflicts;

        loop {
            counter += 1;
            if counter % 1000 == 0 {
                if self.options.debug {
                    eprintln!("stats: {} restarts, {} conflicts, {} decisions, {} propagations",
                              self.stats.restarts, self.stats.conflicts, self.stats.decisions, self.stats.propagations);
                }
            }

            if let Some(confl) = self.propagate() {
                self.stats.conflicts += 1;
                if self.decision_level() == 0 {
                    self.proof.push(String::from("0"));
                    return Some(false);
                }
                let (lev, assert_lits) = self.analyze(confl);
                assert_lits.iter().for_each(|l| self.order.bump(l.var()));
                self.cancel_until(lev);

                let mut learnt_str = String::new();
                for l in assert_lits.iter() {
                    learnt_str.push_str(&format!("{} ", l.to_i32()));
                }
                learnt_str.push_str("0");

                if self.options.save_proof {
                    self.proof.push(learnt_str);
                }

                self.learn(assert_lits);
                self.order.decay();
                self.decay_clauses();
            } else {
                if (self.learnt.len() as i32) - (self.n_assigns() as i32) >= (max_learnts as i32) {
                    if self.options.debug {
                        eprintln!("forgetting");
                    }
                    self.forget();
                }

                if self.n_assigns() == self.n_vars() {
                    return Some(true);
                } else if self.stats.conflicts >= max_conflicts {
                    return None;
                } else {
                    let newlit = self.choose();
                    self.decide(newlit);
                    self.stats.decisions += 1;
                }
            }
        }
    }

    pub fn solve(&mut self) -> bool {
        let mut max_conflicts: usize = self.options.init_max_conflicts;
        let mut max_learnts: usize = self.clauses.len() / 3;

        let out = loop {
            if let Some(out) = self.search(max_conflicts, max_learnts) {
                break out;
            } else {
                self.stats.restarts += 1;
                max_conflicts = ((max_conflicts as f32) * self.options.max_conflicts_multiplier) as usize;
                max_learnts = ((max_learnts as f32) * self.options.max_learnts_multiplier) as usize;
                self.cancel_until(0);
                if self.options.debug {
                    eprintln!("restarting. new parameters are: max_conflicts = {}, max_learnts = {}",
                              max_conflicts, max_learnts);
                }
            }
        };

        out
    }

    pub fn get_proof(&self) -> &Vec<String> {
        &self.proof
    }

    pub fn get_model(&self) -> Vec<i32> {
        let mut model: Vec<i32> = Vec::new();
        for i in 1..(self.model.keys().max_by(|x, y| x.cmp(y)).map(Var::to_u32).unwrap_or_default()+1) {
            match self.model.get(&Var::from_u32(i)) {
                Some(Sign::Pos) => model.push(i as i32),
                Some(Sign::Neg) => model.push(-(i as i32)),
                _ => model.push(-(i as i32)),
            }
        }
        model
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
        let mut solver = Solver::new(SolverOptions::default());
        assert_eq!(solver.add_clause(vec![]), false);
    }

    #[test]
    fn test_add_singleton_clause() {
        let mut solver = Solver::new(SolverOptions::default());
        solver.add_clause(vec![Lit::from_i32(1)]);
        println!("model: {:?}", solver.model);
        assert_eq!(solver.model, HashMap::from([(Var::from_u32(1), Sign::Pos)]));
    }

    #[test]
    fn test_propagation() {
        let mut solver = Solver::new(SolverOptions::default());
        assert_eq!(solver.add_clause(vec![Lit::from_i32(1), Lit::from_i32(2)]), true);
        assert_eq!(solver.add_clause(vec![Lit::from_i32(-1)]), true);
        assert_eq!(solver.propagate(), None);
        assert_eq!(solver.model, HashMap::from([(Var::from_u32(1), Sign::Neg),
                                                (Var::from_u32(2), Sign::Pos)]));
    }

    #[test]
    fn test_conflict_enqueue() {
        let mut solver = Solver::new(SolverOptions::default());
        assert_eq!(solver.add_clause(make_clause(vec![1])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1])), false);
    }

    #[test]
    fn test_conflict_propagation() {
        let mut solver = Solver::new(SolverOptions::default());
        assert_eq!(solver.add_clause(make_clause(vec![1, 2])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-2, 1])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1])), true);
        assert_eq!(solver.propagate().is_some(), true);
    }

    #[test]
    fn test_analyze() {
        let mut solver = Solver::new(SolverOptions::default());
        assert_eq!(solver.add_clause(make_clause(vec![1, 2])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-2, 1])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1])), true);
        let conflict = solver.propagate().unwrap();
        let (lev, assert_clause) = solver.analyze(conflict);
        assert_eq!(lev, 0);
        assert_eq!(assert_clause, make_clause(vec![1]));
    }

    #[test]
    fn test_calc_reason() {
        let solver = Solver::new(SolverOptions::default());
        let clause = Clause::from_lits(make_clause(vec![1, 2, 3]));
        assert_eq!(solver.calc_reason(&clause, Some(Lit::from_i32(3))), Vec::from([Lit::from_i32(1), Lit::from_i32(2)]));
    }

    #[test]
    fn test_propagate_2() {
        let mut solver = Solver::new(SolverOptions::default());
        assert_eq!(solver.add_clause(make_clause(vec![1, 2])), true);
        assert_eq!(solver.add_clause(make_clause(vec![1, -2])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, 2])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, -2])), true);
        solver.decide(Lit::from_i32(1));
        println!("pqueue: {:?}", solver.propq);
        let out = solver.propagate();
        println!("out: {:?}", out);
        assert_eq!(out.is_none(), false);
    }

    #[test]
    fn test_analyze_2() {
        let mut solver = Solver::new(SolverOptions::default());
        assert_eq!(solver.add_clause(make_clause(vec![1, 2])), true);
        assert_eq!(solver.add_clause(make_clause(vec![1, -2])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, 2])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, -2])), true);
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
        let mut solver = Solver::new(SolverOptions::default());
        assert_eq!(solver.add_clause(make_clause(vec![1, 2, 3, 4, 5])), true);
        solver.decide(Lit::from_i32(1));
        solver.decide(Lit::from_i32(2));
        solver.decide(Lit::from_i32(3));
        solver.decide(Lit::from_i32(4));
        solver.cancel_until(0);
        assert_eq!(solver.decision_level(), 0);
        assert_eq!(solver.trail.len(), 0);
    }

    #[test]
    fn test_cancel_2() {
        let mut solver = Solver::new(SolverOptions::default());
        assert_eq!(solver.add_clause(make_clause(vec![1, 2, 3, 4, 5])), true);
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
        let mut solver = Solver::new(SolverOptions::default());
        assert_eq!(solver.add_clause(make_clause(vec![1, 2, 3, 4, 5])), true);
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
    fn test_cancel_4() {
        let mut solver = Solver::new(SolverOptions::default());
        assert_eq!(solver.add_clause(make_clause(vec![1, 2, 3, 4, 5])), true);
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
        let mut solver = Solver::new(SolverOptions::default());
        solver.add_clause(make_clause(vec![1, 2])); // to create lits
        solver.learn(make_clause(vec![-1, -2]));
        let solved_clauses: Vec<Rc<Clause>> = solver.learnt.iter().map(Rc::clone).collect();
        assert_eq!(solved_clauses.len(), 1);
        assert_eq!(solved_clauses[0], Rc::new(Clause::from_lits(make_clause(vec![-1, -2]))));
    }

    #[test]
    fn test_learn_unit() {
        let mut solver = Solver::new(SolverOptions::default());
        solver.add_clause(make_clause(vec![1, 2])); // to create lits
        solver.learn(make_clause(vec![-1]));
        let solved_clauses: Vec<Rc<Clause>> = solver.learnt.iter().map(Rc::clone).collect();
        assert_eq!(solved_clauses.len(), 1);
        assert_eq!(solved_clauses[0], Rc::new(Clause::from_lits(make_clause(vec![-1]))));
        assert_eq!(true, solver.propagate().is_none());
        assert_eq!(Sign::Neg, solver.model[&Var::from_u32(1)]);
        assert_eq!(Sign::Pos, solver.model[&Var::from_u32(2)]);
        assert_eq!(2, solver.model.len());
    }

    #[test]
    fn test_undo_level() {
        let mut solver = Solver::new(SolverOptions::default());
        assert_eq!(solver.add_clause(make_clause(vec![1, 2])), true);
        assert_eq!(solver.add_clause(make_clause(vec![1, -2])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, 2])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, -2])), true);
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
        let mut solver = Solver::new(SolverOptions::default());
        assert_eq!(solver.add_clause(make_clause(vec![1, 2])), true);
        assert_eq!(solver.add_clause(make_clause(vec![1, -2])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, 2])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, -2])), true);
        println!("{:?}", solver.cla_activity);
        assert_eq!(solver.solve(), false);
    }

    #[test]
    fn simple_test_sat() {
        let mut solver = Solver::new(SolverOptions::default());
        assert_eq!(solver.add_clause(make_clause(vec![-1, 2])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-2, 3])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-3, 4])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-4, 1])), true);
        println!("clauses: {:?}", solver.clauses);
        println!("attach: {:?}", solver.attach);
        assert_eq!(solver.solve(), true);
    }

    #[test]
    fn simple_test_sat_2() {
        let mut solver = Solver::new(SolverOptions::default());
        assert_eq!(solver.add_clause(make_clause(vec![1, 2, -3])), true);
        assert_eq!(solver.add_clause(make_clause(vec![1, -2, 3])), true);
        assert_eq!(solver.add_clause(make_clause(vec![1, -2, -3])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, 2, 3])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, 2, -3])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, -2, 3])), true);
        assert_eq!(solver.add_clause(make_clause(vec![-1, -2, -3])), true);

        assert_eq!(solver.propagate().is_some(), false);
        solver.decide(Lit::from_i32(1));
        solver.decide(Lit::from_i32(2));

        let out = solver.propagate();
        assert_eq!(out.is_some(), true);

        let (lev, _alits) = solver.analyze(out.unwrap());
        solver.cancel_until(lev);
        println!("trail: {:?}", solver.trail);
        println!("decision level: {:?}", solver.decision_level());
        println!("reason: {:?}", solver.reason);
        println!("lim: {:?}", solver.lim);
        println!("level: {:?}", solver.level);

        assert_eq!(solver.decision_level(), 1)

        // assert_eq!(solver.solve(), true);
    }

    #[test]
    fn test_duplicate_clause() {
        let mut solver = Solver::new(SolverOptions::default());
        assert_eq!(solver.add_clause(make_clause(vec![1, 2, 3])), true);
        assert_eq!(solver.add_clause(make_clause(vec![1, 2, 3])), true);
        assert_eq!(solver.add_clause(make_clause(vec![1, 2, 3])), true);
        assert_eq!(solver.solve(), true);
    }

    #[test]
    fn test_same_clause() {
        let mut solver = Solver::new(SolverOptions::default());
        assert_eq!(solver.add_clause(make_clause(vec![1, 2, 3])), true);
        assert_eq!(solver.add_clause(make_clause(vec![1, 3, 2])), true);
        assert_eq!(solver.add_clause(make_clause(vec![2, 1, 3])), true);
        assert_eq!(solver.add_clause(make_clause(vec![2, 3, 1])), true);
        assert_eq!(solver.add_clause(make_clause(vec![3, 1, 2])), true);
        assert_eq!(solver.add_clause(make_clause(vec![3, 2, 1])), true);
        assert_eq!(solver.solve(), true);
    }

}

