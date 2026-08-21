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
linear-code incidence part is now closed by
`finitely-presented-oligomorphic-linear-pauli-addresser`: after adjoining the
finitary linear group, bounded vector/covector configurations have finitely
many orbits classified by relation kernels and pairing matrices.  The open
problem is narrower: prove dimension-independent HS consistency between the
different orbit representatives of one occurrence.  The amenable Houghton
version of that addresser is an exact hyperlinear countermodel to every proof
which omits this quantitative gauge step.

## Attempts

- **Global Thompson names.**  Exact Pauli cells exist, but comparing two names
  of one cell along a stabilizer word pays unbounded length and coherent small
  rotations realize the loss.
- **Linear oligomorphic repair.**  Acting first by the finitary linear group
  makes all bounded linearity and symplectic-pairing predicates finite orbit
  types, and the resulting semidirect Pauli tower is finitely presented.  This
  solves the incidence enumeration, but not the normalized-HS section/gauge
  coherence between different representatives.  Choosing an amenable
  addresser makes the whole exact construction hyperlinear and proves that
  this remaining distinction is load-bearing.
- **Direct complete-table tests.**  These fall back to
  `finitely-presented-uniform-area-clifford-tape`, which is stronger than the
  occurrence target and retains the table-area obstruction.
