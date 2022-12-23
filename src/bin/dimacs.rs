use std::env;
use std::fs;
use std::io::{self, BufReader, BufRead};

use cdcl_lib::model::{Clause, Model};

fn main() {

    let input = env::args().nth(1);
    let reader: Box<dyn BufRead> = match input {
        None => Box::new(BufReader::new(io::stdin())),
        Some(filename) => Box::new(BufReader::new(fs::File::open(filename).unwrap()))
    };

    let mut nclauses: i32 = -1;
    let mut _nvars: i32 = -1;
    let mut clauses: Vec<Clause> = Vec::new();

    for lineres in reader.lines() {
        if let Ok(line) = lineres {
            if line.starts_with("c") {
                continue;
            } else if line.starts_with("p") {
                let mut elems = line.split_whitespace();
                _nvars = elems.nth(2).unwrap().trim().parse().unwrap();
                nclauses = elems.nth(0).unwrap().trim().parse().unwrap();
            } else {
                let clause: Clause = line.split_whitespace()
                                 .filter_map(|x| x.trim().parse().ok())
                                 .take_while(|x| *x != 0)
                                 .collect();
                if clause.len() > 0 {
                    clauses.push(clause);
                }
            }
        }
    }

    if clauses.len() != (nclauses as usize) {
        println!("Error. found a different number of clauses than declared");
        std::process::exit(-1);
    }

    // println!("n_vars: {}", _nvars);
    // println!("n_clauses: {}", nclauses);

    // for clause in &clauses {
    //     for l in clause {
    //         print!("{} ", &l);
    //     }
    //     println!("");
    // }

    let mut model: Model = Model::new(clauses);

    let out = model.solve();
    if out {
        println!("satisfied");
    } else {
        println!("unsatisfied");
    }

}
