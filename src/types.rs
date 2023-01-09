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

#[derive(PartialEq, Eq, Hash)]
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

    pub fn neg(&self) -> Lit {
        Lit(-self.0)
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

#[derive(Debug)]
#[derive(PartialEq, Eq, Hash)]
pub struct Clause {
    lits : Box<[Lit]>
}

impl Clause {
	pub fn from_lits(lits: Vec<Lit>) -> Clause {
        match lits.len() {
            0 => panic!("cannot create empty clause"),
            _ => Clause { lits: lits.into_boxed_slice() }
        }
	}

    pub fn lits(&self) -> &[Lit] {
        &self.lits
    }
}

