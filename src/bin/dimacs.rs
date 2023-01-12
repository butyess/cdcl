use std::io::{self, BufReader, BufRead};
use cdcl_lib::solver::{Solver, SolverStats};
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
            println!("c Unsat (found while inserting clauses)");
            println!("s UNSATISFIABLE");
            println!("0");
            std::process::exit(0);
        }
    }

    let out = solver.solve();
    
    let stats: &SolverStats = solver.get_stats();
    println!("c statistics: {} restarts, {} conflicts, {} decisions, {} propagations",
             stats.restarts, stats.conflicts, stats.decisions, stats.propagations);

    match out {
        true => {
            println!("s SATISFIABLE");
            println!("v ");
            for l in solver.get_model() {
                print!("{} ", l);
            }
            println!("");
        }
        false => {
            println!("s UNSATISFIABLE");
            for line in solver.get_proof() {
                println!("{}", line);
            }
        }
    }

}
