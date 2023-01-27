# CDCL SAT Solver

## Compile

Rust's package manager `cargo` is required.

To print stats about the solver process, the solver will read into `/proc/[pid]/stats`,
hence only the linux operating system is supported.

1. Compile with `cargo build --bin dimacs --release`
2. Executable will be in `target/release/dimacs`

## Usage

```
$ target/release/dimacs --help
Usage: dimacs [OPTIONS]

Options:
      --no-model        Hide model when satisfiable
      --no-proof        Hide proof when unsatisfiable
  -f, --from <FROM>     Read from file. If none, reads from stdin
  -o, --out <OUT>       Output to file. If none, outputs to stdout
  -d, --debug           Display information to stderr during solving
      --disable-forget  Wether to use the forget euristic or not
  -h, --help            Print help information
  -V, --version         Print version information
```

