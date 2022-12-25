use either::Either;
use crate::model::{Lit, Var};
use super::model::Clause;

// 1UIP
// WL
// VSIDS
// SUBSUMPTION
// PROPOSITIONAL RESOLUTION PROOF

// Model class: handles WL, the state of variables
// should it have the list of clauses?

type Conflict = Clause;

trait CDCLModel {
    fn assign(&mut self, lit: Lit, justification: Option<&Clause>)
        -> Either<&Conflict, Vec<(Lit, &Clause)>>;

    fn all_variables_assigned(&self) -> bool;

    fn pick_branching_variable(&self) -> Lit;

    fn is_assertion_lit(&self, clause: &Clause) -> Option<Lit>;

    fn resolve(&self, left: &Clause, right: &Clause) -> Clause;
    fn learn(&mut self, clause: Clause);
    fn backjump(&mut self);
}
