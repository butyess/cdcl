// sign and state

#[derive(Debug)]
#[derive(PartialEq, Eq)]
#[derive(Copy, Clone)]
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
#[derive(PartialOrd, Ord)]
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
    
    pub fn to_i32(&self) -> i32 {
        self.0
    }
}

#[derive(Debug)]
#[derive(PartialEq, Eq, Hash)]
#[derive(PartialOrd, Ord)]
#[derive(Copy, Clone)]
pub struct Var(u32);

impl Var {
    pub fn from_u32(v: u32) -> Var {
        Var(v)
    }

    pub fn to_lit(&self, sign: Sign) -> Lit {
        match sign {
            Sign::Pos => Lit::from_i32(self.0 as i32),
            Sign::Neg => Lit::from_i32(-(self.0 as i32)),
            _ => panic!("cannot build from undef sign")
        }
    }

    pub fn to_u32(&self) -> u32 {
        self.0
    }
}

// clause

#[derive(Debug)]
#[derive(PartialEq, Eq, Hash)]
#[derive(PartialOrd, Ord)]
#[derive(Clone)]
pub struct Clause {
    lits : Box<[Lit]>
}

impl Clause {
    pub fn from_lits(lits: Vec<Lit>) -> Clause {
        Clause { lits: lits.into_boxed_slice() }
        // match lits.len() {
        //     0 => panic!("cannot create empty clause"),
        //     _ => Clause { lits: lits.into_boxed_slice() }
        // }
    }

    pub fn lits(&self) -> &[Lit] {
        &self.lits
    }

    pub fn is_unit(&self) -> bool {
        self.lits.len() == 1
    }
}

