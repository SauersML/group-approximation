---
rg: 2
id: binary-strict-pair-small-memory-census-proof
kind: route
title: Decide the word problem of every small forward-relation group, then test every rule against every decoder extension
target: binary-strict-pairs-need-a-memory-with-four-elements
requires:
  - surjunctivity-is-axiomatized-by-rectangle-clauses
artifacts:
  - research/artifacts/gottschalk-small-memory-census-2026-09-13.md
---

Sections 1–3 of the artifact.

1. **Reduction.** Rectangle data of shape `(ns, nm)` realized in a group have a realized forward
   table `T`. The same data are realized in the forward-relation group `P(T)`, whose realized
   forward table is `T`.
   - Equal labels give the same automaton on a smaller memory.
   - A strict pair realized anywhere is strict at `P(T)`'s reverse table.

   So it suffices to check the closed rook-independent tables of shapes `2x2`, `2x3`, `3x2` and
   `3x3`. Shapes with a memory of size one are Proposition 4 of the Boolean-core artifact.
2. **Word problems.** Every table's forward, reverse and label words are decided with proof.
   - *Tietze.* After greedy Tietze elimination, 446 of the 628 tables are cyclic, free, or free
     abelian of rank two. There equality is exponent arithmetic or comparison of reduced words.
     These decisions agree with the oracle on all 436 tables where both decide.
   - *Certificates.* Each of the other 182 tables gets two kinds of certificate:
     - a replayed rewriting derivation for every equal pair;
     - for every distinct pair, a permutation representation that satisfies every relator and
       separates the pair.

     All 182 pass.
3. **Census.** For each closed table with distinct labels and each of the `2^(2^nm)` rules `mu`,
   two independent implementations do the same test.
   - They compute the forced partial decoder when `Dec` holds.
   - They test every constant assignment on the realized reverse classes against every extension of
     that decoder on the tuples it reads.

   Both report no strict data. In shape `3x3` both count 384 closed tables and 1396 rules with
   `Dec`.
