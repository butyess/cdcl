use super::Lit;
use super::Clause;

pub struct DecisionStack<'a> {
    ds: Vec<Vec<(Lit, &'a Clause)>>,
}

impl<'a> DecisionStack<'a> {
    fn decisions(&self) -> i32 {
        self.ds.iter().map(|level| level.len() as i32).sum()
    }
}

