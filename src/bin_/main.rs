#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]
#![allow(unused_imports)]

use cdcl_lib::model::{Clause, Model};

fn main() {
    let clauses: Vec<Clause> = vec![
        vec![1, -2, 3],
        vec![2],
    ];

    let mut model = Model::new(clauses);
    let _out = model.solve();

    // println!("output: {}", out);

}