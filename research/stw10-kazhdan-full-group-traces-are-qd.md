---
rg: 2
id: stw10-kazhdan-full-group-traces-are-qd
kind: claim
title: Every amenable trace on a Kazhdan full group C-star algebra is quasidiagonal
distinct_from:
  stw99-problem-x1-amenable-traces-quasidiagonal: that asks for every amenable trace on every C-star algebra; this proves the full-group-algebra subclass under Kazhdan property T.
  kazhdan-groups-in-hyperfinite-unitary-group-are-rf: that applies the same trace rigidity to one faithful hyperfinite character in order to deduce residual finiteness; this records the underlying conclusion for every amenable trace.
artifacts:
  - GroupApproximation/Manuscript/NinetyNineProblems/KazhdanQuasidiagonalTraces.lean
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

Let `Gamma` be a countable discrete group with Kazhdan's property `(T)`.
Then every amenable tracial state on the full group C-star algebra
`C*(Gamma)` is quasidiagonal.

More precisely, every amenable trace is a pointwise limit of traces of
finite-dimensional unitary representations of `Gamma`.  The corresponding
unital star-homomorphisms into matrices have zero operator-norm
multiplicative defect, so they are quasidiagonal trace models.  Consequently
any full-group-algebra counterexample to STW Problem X(1) must come from a
non-Kazhdan group.

