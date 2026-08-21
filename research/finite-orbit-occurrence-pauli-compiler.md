---
rg: 2
id: finite-orbit-occurrence-pauli-compiler
kind: claim
title: Compile unbounded robust Pauli games through finitely many occurrence-test orbits
distinct_from:
  thompson-clifford-central-product-tape: that globally names exact Pauli cells and then must compare their alternative addresses; this names local test occurrences and makes consistency itself a bounded-arity test orbit.
  finitely-presented-uniform-area-clifford-tape: that asks for the complete multiplication table of every Pauli group with bounded area; this asks only for a robust game's sampled local test relations.
  hs-pcp-boone-compiler: that compiles a machine-indexed verifier with a uniform semantic decoder; this may use one bespoke robust Pauli game family and needs only a dimension witness.
artifacts:
  - research/artifacts/static-challenger-occurrence-hs-breaker-2026-08-20.md
---

OPEN.  Construct one finitely presented group with a nontrivial central
involution `J`, a family of finite robust dimension-witness games `G_N`, and
word representatives for every local test occurrence such that:

1. every involution, commutation, anticommutation, linearity/code, and
   occurrence-consistency check belongs to one of finitely many bounded-arity
   orbits under the addressing group;
2. every instance of a check is a literal conjugate of its prototype relator,
   so a tuple of relator defect `epsilon` yields `(OGC2)` with constants
   independent of `N` and address length;
3. the game soundness theorem turns value above one fixed threshold into a
   local dimension lower bound `D_N->infinity`;
4. the exact crossed-product/infinite-tensor model satisfies all relators and
   keeps `J` nontrivial.

The essential change from global naming is that two occurrences of the same
logical observable need not first be proved equal as matrices.  Their direct
consistency test is part of the game and itself has bounded orbit type.  The
open combinatorial problem is to realize an unbounded robust Pauli/code test
family with finitely many such orbits; high transitivity alone controls
equality patterns but does not automatically encode the required linear-code
incidences.

## Attempts

- **Global Thompson names.**  Exact Pauli cells exist, but comparing two names
  of one cell along a stabilizer word pays unbounded length and coherent small
  rotations realize the loss.
- **Finite-orbit occurrence names.**  Bounded tuple equality patterns do give
  finitely many local orbits, but a robust Pauli-basis game also needs an
  unbounded family of linear-code incidences.  No current Thompson action
  makes all of those incidences finitely many bounded-arity orbits.
- **Direct complete-table tests.**  These fall back to
  `finitely-presented-uniform-area-clifford-tape`, which is stronger than the
  occurrence target and retains the table-area obstruction.
