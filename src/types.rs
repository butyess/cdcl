use std::rc::Rc;

// sign and state

#[derive(Debug)]
#[derive(PartialEq, Eq)]
pub enum Sign { Pos, Neg, Undef }

impl Sign {
    pub fn neg(&self) -> Sign {
        match self {
            Sign::Pos => Sign::Neg,
            Sign::Neg => Sign::Pos,
            Sign::Undef => Sign::Undef,
        }
    }
}

pub enum State { Sat, Unsat, Undef }

// literal and variable

#[derive(Debug)]
#[derive(PartialEq, Eq, Hash)]
#[derive(Copy, Clone)]
pub struct Lit(i32);

impl Lit {
    pub fn from_i32(l: i32) -> Lit {
        Lit(l)
    }

    pub fn var(&self) -> Var {
        Var(self.0.abs() as u32)
    }

    pub fn sign(&self) -> Sign {
        match self.0.is_positive() {
            true => Sign::Pos,
            false => Sign::Neg,
        }
    }
}

#[derive(Debug)]
#[derive(PartialEq, Eq, Hash)]
#[derive(Copy, Clone)]
pub struct Var(u32);

impl Var {
    pub fn from_u32(v: u32) -> Var {
        Var(v)
    }
}

// clause

pub struct SingletonClause(Lit);
pub struct ManyClause {
    first  : Lit,
    second : Lit,
    others : Box<[Lit]>
}

impl SingletonClause {
    pub fn lit(&self) -> Lit {
        self.0
    }
}

impl ManyClause {
    pub fn wl(&self, idx: usize) -> Lit {
        match idx {
            0 => self.first,
            1 => self.second,
            _ => panic!("Bad wl request")
        }
    }

    pub fn wls(&self) -> (Lit, Lit) {
        (self.first, self.second)
    }
}

pub enum Clause { Single(SingletonClause), Many(ManyClause) }

impl Clause {
	pub fn from_lits(mut lits: Vec<Lit>) -> Option<Clause> {
        match lits.len() {
            0 => None,
            1 => Some(Clause::Single(SingletonClause(lits[0]))),
            _ => Some(Clause::Many(ManyClause {
                    first: lits.pop().unwrap(),
                    second: lits.pop().unwrap(),
                    others: lits.into_boxed_slice(),
                }))
        }
	}
}

// assignment

pub struct Assignment {
    pub lit     : Lit,
    pub reason  : Option<Rc<Clause>>
}

