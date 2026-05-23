# unary-scheduling

Unary scheduling: resource assignemnt for a unary resource.

Constraint solving for scheduling tasks on a **unary resource** — a resource that
can only do one thing at a time, so no two tasks may overlap.

## Motivating example: rehearsal scheduling

Suppose you are running rehearsals over the course of a week. Given
a set of students (the staff) and a set of songs (the tasks), we want to
find a rehearsal schedule given:

  - the availabilities of each student across the week,
  - for each song, the group of students that need to play that song together.


There is a single rehearsal slot at any given moment, so rehearsals cannot
overlap: this is the unary resource.

## Project structure

The `schedule-spreadsheet` application reads scheduling data from an
Excel spreadsheet and writes an updated spreadsheet back.

```sh
cabal run schedule-spreadsheet -- INPUTFILE [OPTIONS]
```

`INPUTFILE` is the spreadsheet to read; the `.xlsx` extension is supplied
automatically (so `myschedule` reads `myschedule.xlsx`).

| Option | Default | Meaning |
| --- | --- | --- |
| `INPUTFILE` (positional) | — | Input `.xlsx` spreadsheet to read. |
| `-o`, `--output FILE` | `output.xlsx` | Where to write the updated spreadsheet. |
| `-l`, `--log FILE` | `log.txt` | Where to log how each constraint was derived. |
| `--no-prop` | (propagation on) | Disable constraint propagation entirely. |
| `--no-search` | (search on) | Disable the search for a concrete schedule. |
| `-m`, `--makespan` | off | Enable makespan constraints (**experimental**). |

When search is enabled, a few extra files are written next to the output:
`search_statistics.txt`, `cost.txt`, and `dotfile.txt` (a Graphviz dump of the
precedence graph of the best solution).

Example:

```sh
cabal run schedule-spreadsheet -- rehearsals -o rehearsals-solved -l rehearsals-log.txt
```

### Spreadsheet format

The tool discovers where everything lives from a small block of pointer formulas
in the top-left corner, then reads three regions: a row per task, a row per staff
member, and a block of availability columns shared by both.

#### Control block (cells B1:C3)

Each cell contains a formula `=<cell>` pointing at the first/last boundary of a
region. Only the **row** of the pointed-at cell matters for tasks/staff, and only
the **column** matters for availability.

| Cell | Points at | Meaning |
| --- | --- | --- |
| `B1` / `C1` | any cell in first / last **task** row | range of task rows |
| `B2` / `C2` | any cell in first / last **staff** row | range of staff rows |
| `B3` / `C3` | any cell in first / last **availability** column | range of time-slot columns |

#### Task rows

For each task row:

- **Column A** — the staff assigned to the task, as a formula
  `=TEXTJOIN(delimiter, ignore_empty, cell_1, …, cell_n)` where each `cell_k`
  refers to a cell in the row of an assigned staff member (e.g. their name cell).
- **Column B** — the task duration, as a number of availability columns.
- **Column C** — the task name.
- **Availability columns** — see below.

#### Staff rows

For each staff row:

- **Column C** — the staff member's name.
- **Availability columns** — see below.

(Column B of a staff row is also where makespan constraints go when `--makespan`
is enabled; see the program's `--help` for the format.)

#### Availability values

In every availability column, for both task and staff rows:

- a cell value of `0` means **unavailable**;
- a blank cell (or any other value) means **available**.

#### Output

The output spreadsheet is a copy of the input with:

- task rows: availability cells set to `0` for any slot where the task can no
  longer be scheduled (after propagation, and after search if enabled);
- staff column A: a summary such as `Song A (2) + Song C (1) = 3`.

The log file explains, in plain text, why each slot was removed (which
propagation rule fired and on account of which other tasks).

## Implementation overview

The library implements standard unary-resource constraint-propagation algorithms
over task time windows:

- **prune** (drop windows too short for the task) and **timetable** (block out
  slots a task must occupy) — local propagators;
- **overload checking**, **detectable precedences**, **not-first / not-last**,
  and **edge finding** — global propagators based on Θ-tree / Θ-Λ-tree structures;
- a **precedence matrix** that records and transitively propagates ordering
  decisions.

Propagation runs to a fixpoint. An optional **search** then fixes the
still-unknown pairwise orderings one at a time (with backtracking), keeping
the best solutions found according to a cost function.
