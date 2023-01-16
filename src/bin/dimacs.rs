use std::io::{self, BufReader, BufRead, BufWriter, Write};
use std::path::Path;
use std::fs::File;
use std::time::Duration;
use cpu_time::ProcessTime;
use cdcl_lib::solver::{Solver, SolverStats};
use cdcl_lib::types::Lit;
use clap::Parser;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Hide model when satisfiable
    #[arg(long, default_value_t = false)]
    no_model: bool,

    /// Hide proof when unsatisfiable
    #[arg(long, default_value_t = false)]
    no_proof: bool,

    /// Read from file. If none, reads from stdin
    #[arg(long, short)]
    from: Option<String>,

    /// Output to file. If none, outputs to stdout
    #[arg(long, short)]
    out: Option<String>
}

fn main() -> io::Result<()> {

    // env_logger::builder()
    //     .format_timestamp(None)
    //     .format_level(false)
    //     .format_module_path(false)
    //     .init();

    let cli = Args::parse();

    let reader: Box<dyn BufRead> = match cli.from {
            Some(fname) => Box::new(BufReader::new(File::open(fname)?)),
            None => Box::new(BufReader::new(io::stdin())),
    };

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
        eprintln!("Error. found a different number of clauses than declared");
        std::process::exit(-1);
    } else {
        let mut writer: Box<dyn Write> = match cli.out {
            Some(fname) => Box::new(BufWriter::new(File::create(&Path::new(&fname))?)),
            None => Box::new(BufWriter::new(io::stdout())),
        };

        let start = ProcessTime::try_now().expect("Getting process time failed");


        let mut solver = Solver::new();
        for clause in clauses {
            if !solver.add_clause(clause, false) {
                writeln!(&mut writer, "c Unsat (found while inserting clauses)")?;
                writeln!(&mut writer, "s UNSATISFIABLE")?;
                writeln!(&mut writer, "0")?;
                return Ok(());
            }
        }

        let out = solver.solve();
        let cpu_time: Duration = start.try_elapsed().expect("Getting process time failed");
        
        let stats: &SolverStats = solver.get_stats();
        writeln!(&mut writer, "c statistics: {} restarts, {} conflicts, {} decisions, {} propagations",
                 stats.restarts, stats.conflicts, stats.decisions, stats.propagations)?;
        writeln!(&mut writer, "c solving duration (CPU Time): {} s", cpu_time.as_secs_f64())?;

        match out {
            true => {
                writeln!(&mut writer, "s SATISFIABLE")?;
                if !cli.no_model {
                    write!(&mut writer, "v ")?;
                    for l in solver.get_model() {
                        write!(&mut writer, "{} ", l)?;
                    }
                    writeln!(&mut writer, "")?;
                }
            }
            false => {
                writeln!(&mut writer, "s UNSATISFIABLE")?;
                if !cli.no_proof {
                    for line in solver.get_proof() {
                        writeln!(&mut writer, "{}", line)?;
                    }
                }
            }
        }
        Ok(())
    }
}
