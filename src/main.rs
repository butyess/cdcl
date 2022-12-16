#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]

// TODO: * remove warning at the top
//       * check if is it ok to use i32 for everything
//       * "Model" is not the correct name (state = clauses || model)

mod model;
mod cvsids;
mod decision_stack;

use std::rc::Rc;

use model::{Model, Clause};

fn main() {
    let mut clause1: Clause = vec![1, 2];
    let mut clause2: Clause = vec![4];
    let mut clause3: Clause = vec![5, 4, 1, 2];
    let clauses: Vec<Clause> = vec![clause1, clause2, clause3];

    let mut model: Model = Model::new(clauses);

    dbg!(&model.decision_stack.ds);

    let out = model.unit_propagation();
    dbg!(out);

    let cl = Rc::clone(&model.clauses[1]);
    model.unit_clauses.push((cl, 4));
    dbg!(&model.unit_clauses);

    let out = model.unit_propagation();
    dbg!(out);

    println!("decision stack: {}", &model.decision_stack);

}
