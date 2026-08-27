---
rg: 2
id: fournier-facio-hyperlinear-iff-singular-near
kind: claim
title: Fournier--Facio hyperlinearity is exactly existence of a purely singular essentially free near representation
distinct_from:
  fournier-facio-group-hyperlinear: That is the unresolved yes-or-no property of the explicit group; this is an equivalent witness problem with the normal sector eliminated.
  binary-leavitt-hyperlinear-iff-singular-near: That is the same reduction for the binary Leavitt unit group; this specializes it to the independent torsion-free nonsofic candidate.
  hyperlinear-near-representation-criterion: That permits an arbitrary invariant state for every group; this proves that every witness for this candidate must be purely singular.
---

Let `G` be the finitely presented torsion-free Fournier--Facio group.  The
following are equivalent.

1. `G` is hyperlinear.
2. There are a Hilbert space `H`, a **purely singular** state `phi` on
   `B(H)`, and a `phi`-near representation `pi:G -> U(H)` in the
   Kahl--Schneider state sense such that

   ```text
   phi(pi(g))=0                    for every g != 1.       (FFSN1)
   ```

The invariance/amenability and near-multiplicativity requirements here are
exactly those in the established Kahl--Schneider criterion; `(FFSN1)` is its
essential-freeness, or regular-character, clause.  The new content is only
that the state can, and in fact must, have zero normal part.

Consequently normal states, trace-class densities, finite-rank exhaustions,
and countably additive atomic diagonal states cannot witness a positive
answer for this candidate.  The open positive branch is a genuinely
singular/finitely-additive microstate phenomenon.

