---
rg: 2
id: qutrit-jacobson-residual-has-fixed-polar-gap
kind: claim
title: The live Jacobson residual carries a fixed qutrit polar gap
artifacts:
  - research/qutrit-jacobson-residual-polar-gap-proof.md
distinct_from:
  qutrit-head-exactification-halves-every-carrier: that computes the coarse head-cut masses in the finite K x K envelope; this computes the exact masses on the five-sign raw Jacobson residual.
  binary-jacobson-residual-opposite-polar-has-coarse-quarter-gap: that gives the operator-norm full-polar-or-leakage dichotomy for the residual opposite root; this couples that dichotomy to the odd-order qutrit marginal and obtains a numerical Hilbert--Schmidt terminal.
  one-sided-raw-qutrit-head-bridges-are-residually-finite: that fences arbitrary one-sided root packets abstractly; this identifies the live residual package itself as one-sided and gives its canonical finite counterprofile.
---

Let `F_q` be the order-`3^5` qutrit packet, with projections
`q,R,q-R in C[F_q]`. Let `e=e_res` be the live residual from the
positive-tail Jacobson fold. Its five defining root signs form an elementary
abelian group `N` of order `2^5`, and `e` is a character
idempotent of `N`. Therefore

```text
tau(e)=1/32,
||e q||_2^2       =1/96,
||e R||_2^2       =1/144,
||e(q-R)||_2^2    =1/288.                               (QJR1)
```

These are canonical group-trace identities, not retraction-sector values.
They hold because `F_q intersect N={1}` by coprime orders, so the
identity coefficient of a product from `C[F_q]C[N]` factors.

Put `k=x_31(1)`. The established residual opposite-root theorem gives
the exhaustive alternative

```text
polar(e k e) is unitary in the e-corner,
or
||(1-e)F k F e||_op >= 1/4,                             (QJR2)
```

where `F` is the coarse residual carrier containing `e`. In the first
case, any typed covariance which factors the residual `R` occurrence
through only one residual qutrit-complement occurrence has the fixed gap

```text
liminf ||source-target||_2
 >= 1/12-1/(12 sqrt(2))
 = (sqrt(2)-1)/(12 sqrt(2)) > 0.                        (QJR3)
```

The same target bound holds after conjugating the qutrit packet by any
scalar actor, since a conjugate of `F_q` still has odd order and intersects
`N` trivially.

This does not yet prove nonhyperlinearity. Every group word supporting
`e,k,q,R` lies in the one-sided coefficient group
`EL_28(A_+)`, where

```text
A_+=F_2<S,Q | Q^2=Q, QS=0>.
```

That group is residually finite. Its canonical finite-quotient models retain
`e` with trace `1/32`, retain all three-phase qutrit data, and evaluate
the opposite-root compression exactly. Hence neither branch of `(QJR2)`
is contradictory by itself. A load-bearing continuation must retain the
separate `T`-bearing alternating occurrence: it must either force the
quarter-boundary term to be small or prove one-complement covariance for the
full residual polar. Dropping that typed occurrence returns to an explicit
hyperlinear counterprofile.
