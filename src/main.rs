#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]

// TODO: * remove warning at the top
//       * check if is it ok to use i32 for everything
//       * "Model" is not the correct name (state = clauses || model)

mod model;

use model::Model;
use model::decision_stack::DecisionStack;

fn main() {
    let mut clause1: Vec<i32> = vec![1, 2];
    let mut clause2: Vec<i32> = vec![4];
    let mut clause3: Vec<i32> = vec![5];
    let clauses: Vec<&Vec<i32>> = vec![&clause1, &clause2,  &clause3];

    let decision_stack = DecisionStack { ds : Vec::new() };
    let mut model = Model { clauses: clauses, decision_stack: decision_stack, variables: vec![1, 2, 4, 5] };

    model.solve();

    // solve(clauses);
}
