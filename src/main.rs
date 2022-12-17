// #![allow(dead_code)]
// #![allow(unused_variables)]
// #![allow(unused_mut)]

// TODO: * remove warning at the top
//       * check if is it ok to use i32 for everything
//       * "Model" is not the correct name (state = clauses || model)

mod model;
mod cvsids;
mod decision_stack;

use model::{Model, Clause};

fn main() {
    let clause1: Clause = vec![1, 2];
    let clause2: Clause = vec![1, -2];
    let clause3: Clause = vec![-1, 2];
    let clause4: Clause = vec![-1, -2];
    let clauses: Vec<Clause> = vec![clause1, clause2, clause3, clause4];

    let mut model: Model = Model::new(clauses);

    let out = model.solve();
    if out {
        println!("satisfied");
    } else {
        println!("unsatisfied");
    }

    // dbg!(&model.decision_stack.ds);

    // let out = model.unit_propagation();
    // dbg!(out);

    // let cl = Rc::clone(&model.clauses[1]);
    // model.unit_clauses.push((cl, 4));
    // dbg!(&model.unit_clauses);

    // let out = model.unit_propagation();
    // dbg!(out);

    // println!("decision stack: {}", &model.decision_stack);

}
