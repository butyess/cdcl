// #![allow(dead_code)]
// #![allow(unused_variables)]
// #![allow(unused_mut)]
// #![allow(unused_imports)]

use std::io::{self, BufReader, BufRead};
use cdcl_lib::solver::Solver;
use cdcl_lib::types::Lit;

fn main() {

    env_logger::builder()
        .format_timestamp(None)
        .format_level(false)
        .format_module_path(false)
        .init();

    let reader: Box<dyn BufRead> = Box::new(BufReader::new(io::stdin()));

    let mut nclauses: i32 = -1;
    let mut _nvars: i32 = -1;
    let mut clauses: Vec<Vec<Lit>> = Vec::new();

    for lineres in reader.lines() {
        if let Ok(line) = lineres {
            if line.starts_with("c") {
                continue;
            } else if line.starts_with("p") {
                let mut elems = line.split_whitespace();
                _nvars = elems.nth(2).unwrap().trim().parse().unwrap();
                nclauses = elems.nth(0).unwrap().trim().parse().unwrap();
            } else {
                let lits: Vec<Lit> = line.split_whitespace()
                                 .filter_map(|x| x.trim().parse().ok())
                                 .take_while(|x| *x != 0)
                                 .map(Lit::from_i32)
                                 .collect();
                if lits.len() > 0 {
                    clauses.push(lits);
                }
            }
        }
    }

    if clauses.len() != (nclauses as usize) {
        println!("Error. found a different number of clauses than declared");
        std::process::exit(-1);
    }

    let mut solver = Solver::new();
    for clause in clauses {
        if !solver.add_clause(clause, false) {
            println!("Unsat (found while inserting clauses)");
        }
    }

    match solver.solve() {
        true => println!("Sat"),
        false => println!("Unsat"),
    }
    
    solver.print_stats();

}
