pub struct Lit(i32);
pub struct Var(u32);

#[derive(Debug, Eq, PartialEq)]
pub enum Sign { Pos, Neg, Undef, }

pub struct Clause {
    lits : Box<[Lit]>
}

impl Clause {
	pub fn from_vec(lits: Vec<Lit>) -> Clause {
		Clause{ lits : lits.into_boxed_slice() }
	}
}

pub type ConflictClause = Clause;
pub type UnitClauses = VecDeque<(Rc<Clause>, Lit)>;

#[derive(Debug)]
pub enum SolverState { Propagating(UnitClauses), Resolving(ConflictClause) }

pub type Assignment = HashMap<Var, VarState>;
pub type DecisionStack = Vec<(i32, Lit, Option<Rc<Clause>>)>;
pub type ResolutionProof = Vec<(Clause, Clause, Clause)>;

