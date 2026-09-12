---
rg: 2
id: moving-basin-truncation-firewall-proof
kind: route
title: Spectrally truncate endpoint displacement and exhibit a collapsing-basin cubic
target: moving-basin-blowup-needs-displacement-charge
requires:
  - fixed-core-passive-fiber-has-positive-basin
  - authenticated-core-union-basin-is-relative-liftability
  - sublinear-bs-block-surgery-is-invisible-to-relative-liftability
  - iwahori-uniform-infinitesimal-rigidity
---

For `(MBB3)`, decompose `D_n=D_n(1-Q_n)+D_nQ_n`.  The first summand has
operator norm at most `tau`, and the second has Frobenius square at most
`4q_n`.  Orthogonality of the right spectral supports gives

```text
||D_n||_2^2
 <=tau^2(1-q_n/d_n)+4q_n/d_n
 <=tau^2+4q_n/d_n.
```

This proves the positive-density displacement bound.  In particular no
choice of thresholds `tau_n->0` can simultaneously leave an operator-small
remainder and move only `o(d_n)` dimensions when `(MBB1)` holds.

The scalar family `(MBB5)` has no zero except `0`, because the quadratic
factor is strictly positive.  Its derivative at that zero is `1+e`, while
its coefficients and all derivatives are uniformly bounded for
`0<e<=1`.  Evaluation at `1` proves `(MBB6)`.  Thus even the exact abstract
ingredients used by a Newton argument--compact coordinate zero sets,
uniformly injective derivative at every zero, and a fixed polynomial degree--
permit the global basin radius to collapse.

In the arithmetic problem, the limiting new zero is the exact relative
ultraproduct homomorphism.  Producing coordinate zeros near it is precisely
`authenticated-core-union-basin-is-relative-liftability`; tangent coercivity
at already lifted coordinate zeros cannot perform that step.
