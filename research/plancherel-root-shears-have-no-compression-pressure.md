---
rg: 2
id: plancherel-root-shears-have-no-compression-pressure
kind: claim
title: Fixed Plancherel root shears alone have no one-to-two compression pressure
invalidates:
  - affine-leavitt-decoder-from-one-invariant-root-window
distinct_from:
  steinberg-root-shear-plancherel-covariance: that proves the available Fourier covariance; this proves why covariance on one common invariant window cannot by itself yield active-mass decay.
  relative-leavitt-active-subspaces-expand-by-two: that gives genuine coefficient-space expansion; this shows that an invariant Fourier window forgets precisely that boundary.
  single-affine-leavitt-branch-chart-is-stationary: that produces exact finite countermodels for the isolated finite-head HNN chart; this is the analogous stationary-law obstruction inside a fixed root-character window.
---

Let `H` be finite abelian and let `alpha_1,...,alpha_l` be automorphisms of
`H`.  On the Fourier atoms `dual(H)`, each dual map is a permutation.  Hence
for any nonnegative weights `c_j` with `sum_j c_j=1`, the transport matrix

```text
T=sum_j c_j P_(alpha_j^*)                                (PRN1)
```

is doubly stochastic and the Plancherel vector is fixed:

```text
T (1/|H|,...,1/|H|)=(1/|H|,...,1/|H|).                  (PRN2)
```

Consequently no strict scalar contraction, Hall deficit, or loss of total
Fourier mass follows from a fixed collection of full shear covariances on one
common invariant row-root window.  Counting several shears as several
branches does not change this: without a disjoint-range or Gram estimate it
counts the same source mass several times.

Applied to `steinberg-root-shear-plancherel-covariance`,
this rules out a decoder which:

1. exactifies one finite row-root group;
2. retains only its Plancherel atom traces; and
3. uses the normalizing shears merely as full atom permutations.

The algebraic doubling in `relative-leavitt-active-subspaces-expand-by-two`
occurs because a finite coefficient window cannot be invariant under both
branch maps.  A live normalized-HS proof must therefore expose and charge
that escaping boundary, or use paired root triangles to prove a disjoint
range/Gram inequality before averaging.  The fixed invariant-window data
alone are stationary.
