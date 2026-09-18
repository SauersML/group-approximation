---
rg: 2
id: baumslag-solitar-gap-table-at-five-by-five
kind: claim
title: A five-by-five forward table in BS(2,3) is a gap table, so finite quotients cannot extend the memory census past four by four, while soficity still kills the table
distinct_from:
  strict-pairs-need-a-memory-with-five-elements: that decides every four-by-four table by finite quotients of its table group and finds no gap table; this exhibits a realizable five-by-five table whose table group is BS(2,3), which has a reverse pair that no finite quotient separates, so that method cannot decide shape five by five.
  strict-automata-live-on-canonical-table-groups: that reduces a rule pair to canonical table groups and notes that sofic quotients kill hinge words; this is one explicit table where the finite-quotient test fails and the sofic test succeeds, and it shows the two tests really differ at shape five by five.
  binary-strict-pairs-need-a-memory-with-four-elements: that solves binary rules up to shape three by three; this uses no rules and is about which certificate a census at shape five by five needs.
  sofic-groups-are-surjunctive: that is the Gromov-Weiss theorem; this applies it to the table group of one gap table.
artifacts:
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/RESULTS.md
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/bsgroup.py
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/gaptable.py
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/bsgapsearch.py
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/extend.py
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/verify_gap55.g
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/gap_tables_5x5.jsonl
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/gap_tables_5x6.jsonl
---

**ESTABLISHED** by `baumslag-solitar-gap-table-at-five-by-five-proof`. The proof is by hand. The scripts find the
table and check it independently.

Notation is from `strict-pairs-need-a-memory-with-five-elements`:

- `T_f(G)` is the forward table, the partition of `S x M` by `sm`.
- `P(T)` is the table group.
- A **gap table** is a table that is realizable but not resolved: some pair of reverse cells
  `x_m x_s != x_m' x_s'` in `P(T)` is merged in every finite quotient of `P(T)`.

**Theorem.** In `G = BS(2,3) = <a, t | t a^2 t^-1 = a^3>` put

```text
S = {1, a, t, a^3, t^-1 a t a^-1},      M = {1, a, a^2, t, t^-1 a t}.
```

1. `T = T_f(G)` has exactly seven coincidences:
   - `a*1 = 1*a`, `a*a = 1*a^2`, `t*1 = 1*t`, `a*a^2 = a^3*1`;
   - `(t^-1 a t a^-1)*a = 1*(t^-1 a t)`, `a*t = t*(t^-1 a t)`, `t*a^2 = a^3*t`.
2. Tietze moves reduce `P(T)` to `<x_a, x_t | x_t x_a^2 x_t^-1 = x_a^3>`. So `x_c -> c` is an isomorphism
   `P(T) -> G`.
3. The reverse cells `a * (t^-1 a t a^-1)` and `(t^-1 a t) * 1` are distinct in `P(T)`. They are equal in every
   finite quotient of `P(T)`. So `T` is a gap table of shape `5x5`.
4. `P(T)` is sofic, hence surjunctive. So no group and no alphabet give a strict pair whose forward table is `T`.

**What this rules out (obstruction).** The resolution lemma of `strict-pairs-need-a-memory-with-five-elements`
(separate reverse cells by finite quotients of `P(T)`) cannot decide every table of shape `5x5`. It fails at
the separation step, on this table. Any census at shape `5x5` or larger must therefore use a certificate that sees
more than the profinite completion of `P(T)`. Soficity of `P(T)` (through the pullback of
`strict-automata-live-on-canonical-table-groups`) is enough here. The largest residually finite quotient of
`P(T)` is `Z[1/6] x| Z`, which is amenable. But that quotient is not the table group, and it merges the gap pair,
so it cannot replace `P(T)` in the lemma.

The same obstruction holds at `5x6`: `gap_tables_5x6.jsonl` has two tables with the same table group.

**What stays open.**

- *First gap shape.* `5x5` is not minimal. `gap-tables-first-appear-at-three-by-six-and-four-by-five` gives gap
  tables at `4x5` and `3x6`, and proves that no smaller shape has one. The `4x5` table uses `t^-1 a t` in `S`. That
  element lies outside the radius-2 ball, which is why the directed search of this experiment missed it.
- *Gap tables that matter.* A gap table can host a counterexample only if its table group is not surjunctive. By
  universality of table groups, some shape has a table whose group is not residually finite. Whether some table
  group of bounded shape is non-sofic is a separate and much harder question.

## Attempts

- The finite-quotient census method, extended to `5x5`, is dead as a complete decision procedure. The exact
  failing step is the separation of `a * (t^-1 a t a^-1)` from `(t^-1 a t) * 1` in `BS(2,3)`.
