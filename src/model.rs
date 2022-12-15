pub mod decision_stack;

use self::decision_stack::DecisionStack;

type Lit = i32;
type Clause = Vec<Lit>;

pub struct Model<'a> {
    clauses: Vec<&'a Clause>,
    decision_stack: DecisionStack<'a>,
    variables: Vec<Lit>,
}

fn print_type_of<T>(_: &T) {
    println!("{}", std::any::type_name::<T>())
}

impl<'a> Model<'a> {
    // implement these functions
    // fn unit_propagation() -> Option<CONFLICT??> {}

    // fn all_variables_assigned() -> bool {}

    // fn make_decision() {}

    // fn resolve_conflict(conflict: CONFLICT??)

    pub fn solve(&mut self) -> bool {
        if let Some(conflict) = self.unit_propagation() {
            return false;
        }

        while !self.all_variables_assigned() {
            self.make_decision();
            if let Some(conflict) = self.unit_propagation() {
                match self.resolve_conflict(conflict) {
                    true => { continue; }
                    false => { return false; }
                }
            }
        }

        return true;
    }
}


