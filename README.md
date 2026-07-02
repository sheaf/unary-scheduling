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

The `unary-scheduling-test` testsuite contains simple property tests relating to
propagators and the underlying data representation of time intervals.

The `unary-scheduling-z3-test` testsuite validates the implementation against Z3.
It validates both:

  1. The SAT-solver core that underlies CDCL.
  2. The unary scheduling solver.

### Benchmarking

The `bench-unary-scheduling` benchmark compares the performance of the
implementation against Z3 and MiniZinc Chuffed. Aga

The `lcg-inspect` executable is the instrumentation framework for the implementation.
It's used:

  1. To inspect generated Core, STG, etc.
  2. For profiling reports.
  3. For instrumentated reports (e.g. numbers of learnt clauses, number of
     search decisions, etc).
  4. For parameter sweeps, e.g. to determine the performance impact of solver
     options or to compare performance across a series of benchmarks.
