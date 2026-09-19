---
rg: 2
id: atlas-ultradeep-prefix-bounded-closure-proof
kind: route
title: Tensor the coherent Schrödinger enemy with the regular Atlas tag and apply the sharp rectangular no-gos
target: atlas-ultradeep-prefix-tower-survives-bounded-scalar-closures
requires:
  - atlas-ef-dual-rows-create-the-prefix-depth-tower
  - finite-tags-do-not-atomize-heisenberg-schrodinger-tower
  - orthogonal-heisenberg-self-copy-skeleton-has-marked-microstates
  - finite-positive-root-fragments-have-marked-regular-models
  - paired-prefix-shears-have-bounded-joint-approximate-rank
  - dual-prefix-renyi2-rate-is-critical-under-rectangular-escape
  - whitehead-swap-copy-completion-retains-rectangular-escape
  - one-coarse-to-fine-prefix-isometry-closes-the-reservoir
---

Put `N=2^n` in the Schrödinger tower of
`finite-tags-do-not-atomize-heisenberg-schrodinger-tower`.  Its formulas
`(FTH1)--(FTH5)` give compatibility, the marked scalar `-I`, atom trace
`2^(-N)`, and commutant gauge `U(2^(M-N))`.  Take the fixed tag in `(FTH3)`
to be the left regular representation of `A8`.  Tensor products preserve
all tower relations and give the exact regular character on the finite
Atlas factor, while `(FTH2)--(FTH5)` are unchanged.  This proves
`(AUP1)--(AUP3)`.

The coordinate-permutation implementers of
`orthogonal-heisenberg-self-copy-skeleton-has-marked-microstates` implement
both branch embeddings and all prescribed transverse shears on each finite
window.  Independently,
`finite-positive-root-fragments-have-marked-regular-models` closes every
finite literal positive-root diagram, including the synchronized range-sum
fold, inside a finite algebra group while retaining the marked root.  These
two exact calibrations show that enlarging either finite window cannot yield
a uniform HS payment.

`paired-prefix-shears-have-bounded-joint-approximate-rank` gives the claimed
common approximate-rank model for every fixed tuple of scalar phase rows.
`dual-prefix-renyi2-rate-is-critical-under-rectangular-escape` proves that
the address rate is exactly critical and supplies the sharp rectangular
countermodel.  Finally,
`whitehead-swap-copy-completion-retains-rectangular-escape` proves `(AUP4)`
with zero defect for every fixed chain of canonical diagonal copy cells.
These are separate exact obstructions to the four proposed closure
mechanisms; no simultaneous model of unrelated full-packet mixed words is
asserted.

The positive endpoint follows from
`one-coarse-to-fine-prefix-isometry-closes-the-reservoir`: after coarse and
fine packet exactification on one projection `P`, one authenticated
coarse-to-fine Gram/covariance row gives

```text
tr(P) <= 4 ||e-X^*X||_2^2,
```

or directly the selector-covariance trace floor.  Thus a non-scalar
same-reservoir row is sufficient, while the preceding exact enemies prove
that none of the four bounded scalar closures provides it.
