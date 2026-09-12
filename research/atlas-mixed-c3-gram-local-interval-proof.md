---
rg: 2
id: atlas-mixed-c3-gram-local-interval-proof
kind: route
title: Substitute the common product and rotate the collision trivial-sign block
target: atlas-mixed-c3-gram-has-local-zero-interval
requires:
  - atlas-common-u-is-twelve-double-coset-system
  - atlas-common-u-c3-compression-is-two-covariance-residuals
  - atlas-19243-has-continuous-regular-s3-line-holonomy
  - atlas-a4-two-c3-line-carriers-have-exact-angle-gap
---

Gauge invariance follows immediately from

```text
(X_eW_e)R(W_e^(-1)Y_e)=X_eRY_e,
```

because `W_e` commutes with `R`.  The common-product equations make this
product independent of `e`, proving the first assertion.

The map `Z` is a compression of the unitary `C(U)` between two projections of
normalized trace `1/6`.  Hence its squared Hilbert--Schmidt norm is at most
either endpoint trace.  Orthogonal projection in Hilbert--Schmidt space gives
`Lambda<=||Z||_2^2`, proving `(MCG4)`.

On `triv directSum sign`, write the moving real reflection relative to
`s=diag(1,-1)` as

```text
c_theta=[[cos(2theta),sin(2theta)],
         [sin(2theta),-cos(2theta)]].                  (MCG10)
```

The idempotents `E_K^+` and `E_K^-` select respectively the trivial and sign
lines.  Thus their off-diagonal compression of `c_theta` is
`sin(2theta)` times one matrix unit.  The two standard blocks contribute
nothing to this compression.  Normalizing by dimension six proves `(MCG5)`.
Linearity of `Z->Z-PZP` proves `(MCG6)`.

The vectorized `Z_*` lies in the K line carrier and is orthogonal to the
common scalar.  Apply the established angle inequality to get the lower bound
in `(MCG7)`; contractivity gives the upper bound.  Continuity of
`sin(2theta)^2`, together with exact collision and regular margins for every
`theta`, proves `(MCG8)`.  Compact semialgebraicity and amplification of
`(MCG9)` follow from the established double-coset system.
