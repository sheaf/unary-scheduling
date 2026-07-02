# unary-scheduling

Given a collection of tasks, each with pre-determined lengths and availabilities,
unary scheduling is the problem of finding a valid schedule for all the tasks
so that no two tasks are performed at the same time.

## Motivating example: rehearsal scheduling

We are given a set of musicians and a set of pieces. Each musician has a fixed
availability (e.g. John is available on Monday from 2pm to 6pm). Each piece
to rehearse has a fixed roster (e.g. Annie, Mark and John need to rehearse
"Giant Steps" together) and a set amount of rehearsal time (e.g. 40 minutes).

The problem is to find a rehearsal schedule: a feasible start time for the
rehearsal of each piece, allowing each piece to be rehearsed sequentially.

## Project architecture

This library tackles unary scheduling through constraint programming:

  - Basic constraint propagation is performed using Vilím's Θ-tree unary resource
    propagators.
  - We search for valid schedules using conflict-driven clause learning (CDCL).

Each propagator explains its inferences as clausal reasons, which allows
interleaving propagation and search decisions.

### schedule-spreadsheet

The `schedule-spreadsheet` application reads scheduling data from an
Excel spreadsheet and writes an updated spreadsheet back.

```sh
cabal run schedule-spreadsheet -- INPUTFILE [OPTIONS]
```

Pass `--help` for an overview of available options and an explanation of how
to set up the spreadsheet for consumption by the executable.

### Testing

The `sanity-tests` testsuite contains simple property tests relating to
propagators and the underlying data representation of time intervals.

The `test-sat-solver` testsuite validates the SAT solver core that underlies
CDCL against Z3.

The `test-scheduling` testsuite validates the unary scheduling solver against
Z3.


### Benchmarking

The `bench-sat-solver` benchmark suite compares the performance of the SAT
solver implementation against Z3.

The `bench-scheduling` benchmark compares the performance of the unary
scheduling solver against Z3 and MiniZinc Chuffed.

The `inspect-unary-scheduling` executable is the instrumentation framework for the implementation.
It's used to:

  1. Inspect generated Core, STG, etc. Tip: use `-f inspect-dumps`.
  2. Generate profiling reports.
  3. Provide instrumentated reports (e.g. numbers of learnt clauses, number of
     search decisions, etc).
  4. Run parameter sweeps. This can be used both to determine the performance
     impact of various solver options and to compare performance across a series
     of benchmarks (e.g. mining hard scheduling benchmarks).
