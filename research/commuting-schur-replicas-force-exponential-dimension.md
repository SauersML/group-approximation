---
rg: 2
id: commuting-schur-replicas-force-exponential-dimension
kind: claim
title: Commuting replicas of a gapped BCS Schur packet force exponential matrix dimension
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  non-ce-bcs-has-finite-dimensional-forbidden-mass-gap: that gives a constant total forbidden mass in one finite-dimensional BCS tuple; this tensors independent packet cocycles across replicas and converts that average mass into exponential representation dimension.
  infinite-index-does-not-force-supercritical-site-rank: that shows every externally fixed finite tensor window remains exactly realizable in sufficiently large dimension; this computes the exponential price of that realization and explicitly does not cross the same-model threshold.
  multiplicity-surplus-is-blind-to-the-non-ce-input: that warns a beta-only mechanism cannot itself distinguish non-CE from classical unsatisfiability; this is only a finite-rank dimension lower bound and makes no nonhyperlinearity claim.
---

Let `B` have `C` contexts and finite-dimensional forbidden-mass floor
`beta_B>0`.  Form `N` mutually commuting replicas of its selector tuple and
attach the Schur packet and flip square for every context violation predicate.
Assume the site packet algebras and flip stable letters commute across
distinct replicas, and restrict an exact finite-dimensional representation to
the marked carrier `J=-1` of dimension `d_-`.

Then

```text
d_- >= 2^(ceil(beta_B N/C)).                                    (CSE1)
```

More precisely, in each replica `i` some context `c_i` has forbidden spectral
mass at least `b=beta_B/C`.  The resulting forbidden projections `Q_i` commute
across replicas.  Their joint spectral decomposition contains a nonzero sector
on which at least `ceil(bN)` of them equal one.  On every minimal refinement of
that sector, those forbidden sites contribute independent Schur flip cocycles,
so their binary projective commutator form has rank at least
`2 ceil(bN)`.  Projective holonomy forces the external multiplicity, hence the
sector dimension, to be divisible by `2^(ceil(bN))`, proving `(CSE1)`.

This is an exact finite-window amplification theorem.  It proves that copied
bad regions cannot all be absorbed cheaply, even when the violated context
varies from replica to replica.  It does **not** give a nonhyperlinear group:
for every fixed `N` the required dimension is finite, and the local gap
`beta_B` could equally come from a classically unsatisfiable CSP.  A final
controller must choose `N` from the current residual dimension or recover a
coherent infinite replica family with uniform HS loss.

