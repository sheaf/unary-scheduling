# `lcg-inspect` — single-benchmark inspection harness

A self-contained executable that runs **one** scheduling benchmark through the
LCG search. It depends only on `unary-scheduling` (no `tasty`, `tasty-bench`, or
Z3), so its compiled output is clean and representative for low-level inspection.

It runs the chosen instance twice:

1. `lcgSearch @MonitoringOff` — the production path, with all instrumentation
   erased by GHC. Timed over a few iterations (coarse wall-clock; use the
   `unary-scheduling-bench` suite for rigorous numbers) and reporting the
   always-on `SearchStats`.
2. `lcgSearch @MonitoringOn` — fully instrumented, reporting the `MonitorReport`
   (per-propagator invocations, propagation rounds, channeling calls, derived
   edges, theory conflicts, reason-clause lengths).

## Choosing the benchmark

Edit `theInstance` (and optionally `iterations`) at the top of
[`Main.hs`](Main.hs). The available instance families live in
`Schedule.Bench.Instances`.

## Running

```sh
cabal run lcg-inspect
```

## Inspecting the compiled output

Dump GHC Core and STG (written next to the build artifacts under
`dist-newstyle/.../lcg-inspect-tmp/*.dump-simpl`, `*.dump-stg-final`):

```sh
cabal build lcg-inspect -f inspect-dumps
```

Late cost-centre profile + GC/allocation stats (the `late-toplevel` detail
places cost centres *after* inlining, so hot spots aren't hidden inside their
callers):

```sh
cabal run lcg-inspect --enable-profiling --profiling-detail=late-toplevel -- +RTS -p -s
```

## Zero-cost check

The instrumentation is dispatched on a phantom mode (`Schedule.Monitor`); the
`@MonitoringOff` specialisation should erase every monitor hook. After
`cabal build lcg-inspect -f inspect-dumps`, the `solveRaw`/`@MonitoringOff`
Core in `*.dump-simpl` should contain no `MonitorOn`, `modifyMutVar'`, or
`tick*` references, whereas the `@MonitoringOn` Core should.
