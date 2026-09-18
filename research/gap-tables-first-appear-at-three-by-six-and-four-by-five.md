---
rg: 2
id: gap-tables-first-appear-at-three-by-six-and-four-by-five
kind: claim
title: The minimal shapes of forward gap tables are exactly three by six and four by five, so finite quotients rule out strict pairs with memories of sizes three and five but stop one step later
distinct_from:
  strict-pairs-need-a-memory-with-five-elements: that decides every table up to four by four by finite quotients; this adds the three-by-five census (so strict pairs with a three-point and a five-point memory are ruled out), proves that no table with a side of size two is a gap table, and exhibits gap tables at three by six and four by five, which settles every minimal gap shape.
  baumslag-solitar-gap-table-at-five-by-five: that exhibits one gap table at five by five and leaves open whether a gap table of shape four by five exists; this gives gap tables at four by five and three by six and proves that no smaller shape has one.
  three-point-decoder-memory-injective-ca-are-surjective: that open claim allows any encoder memory; this proves the case of an encoder memory with at most five points, and shows that the finite-quotient method cannot reach six encoder points.
  amenable-decoder-memory-forces-surjectivity: that handles two-point decoder memories through amenability of the generated group; this proves only the table statement for two-row tables (the table group is a free product of cyclic groups) and uses no measure.
artifacts:
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/RESULTS.md
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/enumtables6.c
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/census_3x5.jsonl.gz
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/census_5x3.jsonl.gz
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/verify_gap36.g
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/schreiersearch.py
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/gaptable.py
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/bsgroup.py
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/gap_tables_3x6.jsonl
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/gap_tables_3x12.jsonl
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/gap_tables_4x5.jsonl
---

**ESTABLISHED** by `gap-tables-first-appear-at-three-by-six-and-four-by-five-proof`. The gap tables and the
two-row case are proved by hand. The `3x5` and `5x3` cases are computer-assisted, with every separation witness
replayed by the independent checker of the `4x4` census.

Notation is from `strict-pairs-need-a-memory-with-five-elements`:

- A forward table `T` of shape `|S| x |M|` is a rook-independent partition of `S x M`.
- `P(T)` is its table group.
- A **gap table** is a realizable table with a pair of reverse cells that is distinct in `P(T)` and merged in every
  finite quotient of `P(T)`.
- A **gap shape** is a shape that carries a gap table.

**Theorem.**

1. *(Two rows.)* If `|S| <= 2` or `|M| <= 2`, then `P(T)` is a free product of a cyclic group and a free group. So
   no such table is a gap table.
2. *(Three by five.)* No table of shape `3x5` or `5x3` is a gap table.
3. *(Three by six.)* In `BS(2,3) = <a, t | t a^2 t^-1 = a^3>`, the memories
   `S = {1, t, ta}` and `M = {1, a, a^-1, a^-2, a^-1 t^-1 a, a^-2 t^-1 a}` give a gap table with `P(T) = BS(2,3)`.
   Its gap pair is `(a^-1 t^-1 a) * t` versus `(a^-2 t^-1 a) * (ta)`.
4. *(Four by five.)* With `u = t^-1 a t`, the memories `S = {1, a, t, u}` and `M = {1, a, t, u, u^2}` give a gap table
   with `P(T) = BS(2,3)`. Its gap pair is `a * u` versus `u * a`.
5. *(Up-set.)* Gap shapes are closed under enlarging either side and under transposition.

So the minimal gap shapes are exactly `3x6`, `4x5`, `5x4` and `6x3`. A shape is not a gap shape iff it has a side of
size at most two or is one of `3x3`, `3x4`, `3x5`, `4x4` and their transposes.

**Corollary (Gottschalk case).** Over every group and every finite alphabet, an injective cellular automaton `tau`
with a left inverse `sigma` is surjective when one of the memories of `tau` and `sigma` has at most three elements
and the other has at most five. This extends `strict-pairs-need-a-memory-with-five-elements` (both at most four), by
the same resolution lemma.

**What this rules out (obstruction).** The finite-quotient census cannot decide shape `3x6` or `4x5`. The failing
step is the separation of `a u` from `u a` in `BS(2,3)`, whose largest residually finite quotient `Z[1/6] x| Z` merges
them. Any extension of the census past these shapes needs a certificate beyond the profinite completion of `P(T)`,
such as soficity. `BS(2,3)` is sofic (Section 5 of `baumslag-solitar-gap-table-at-five-by-five-proof`), so these
tables still host no strict pair.

**How the tables were found.** `schreiersearch.py` fixes a memory `S` and grows `M` through the coincidence graph of
`S` (edges `m -- s'^-1 s m`), enumerating connected sets containing `1` with the ESU algorithm. It keeps a pair when a
reverse pair agrees in `Z[1/6] x| Z` but not in `BS(2,3)`, and Tietze elimination certifies `P(T) = BS(2,3)` through an
explicit inverse map. With `S` drawn from the radius-2 ball it finds nothing at `3x4` or `3x5` and four tables at
`3x6`. A hand-built `3x12` table (`gap_tables_3x12.jsonl`) came first.

**What stays open.**

- *Non-sofic table groups.* A gap table can host a counterexample only if `P(T)` is not surjunctive. Every gap table
  found so far has table group `BS(2,3)`, which is sofic. Is some table group of shape `3xN` non-sofic, or not
  surjunctive? For `|S| = 3` a negative answer at every `N` would settle the bounded-encoder-memory cases of
  `three-point-decoder-memory-injective-ca-are-surjective`.
- *A census at 3x6 with a sofic certificate.* Every `3x6` table that finite quotients do not resolve would need its
  table group certified sofic (for example residually amenable, or built from Baumslag-Solitar pieces).

## Attempts

- The finite-quotient census, extended past `3x5` or `4x4`, is dead as a complete decision procedure. The exact
  failing step is the separation of `a u` from `u a` in `BS(2,3)`, at the tables of items 3 and 4.
