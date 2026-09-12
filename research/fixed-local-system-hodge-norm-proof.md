---
rg: 2
id: fixed-local-system-hodge-norm-proof
kind: route
title: Whitney and smoothed de Rham maps have rank-independent operator norms
target: fixed-complex-unitary-local-system-hodge-norms-are-uniform
requires: []
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

Choose a finite good cover, subordinate partition of unity and one fixed
triangulation of `X`.  In a parallel trivialization of a flat unitary bundle,
all transition maps are unitary.  The usual Whitney construction therefore
gives a cochain map

```text
W_E:C^*(X;E)->Omega^*(X;E)                              (1)
```

whose operator norm is bounded by a constant depending only on the finitely
many scalar Whitney forms and cell incidences.  Tensoring their scalar
coefficient matrices with unitary parallel transports does not change this
bound, so it is independent of `rank(E)` and of the holonomy.

In the other direction, first apply a fixed local de Rham regularization
commuting with `d`, then integrate over cells.  This gives a bounded cochain
map

```text
R_E:Omega^*_(L2)(X;E)->C^*(X;E).                        (2)
```

The smoothing, trace and integration constants are again scalar local
constants; unitary parallel transport preserves fiber norms.  The standard
de Rham--Whitney homotopies show that `W_E` and `R_E` induce inverse maps on
cohomology.  The construction respects the fixed absolute or relative
boundary conditions.

Let `||.||_cell` denote the quotient norm.  If `a` is a minimum-norm cellular
representative, analytic harmonic minimization and (1) give

```text
||[a]||_harm <= ||W_E a||_(L2) <= ||W_E|| ||[a]||_cell. (3)
```

Conversely, if `omega` is the analytic harmonic representative, (2) gives

```text
||[a]||_cell <= ||R_E omega|| <= ||R_E|| ||[a]||_harm.  (4)
```

The rank-independent bounds for `W_E` and `R_E` prove `(ULH2)`.  Notice that
no inverse Laplacian or smallest positive eigenvalue appears; possible small
local-system eigenvalues therefore do not affect the constants.
