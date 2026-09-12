---
rg: 2
id: stw81-fibrewise-absorption-global-colour-collapse-proof
kind: route
title: Globalize fibrewise O-infinity absorption before counting colours
target: stw81-fibrewise-oinfinity-absorption-collapses-base-colours
requires:
  - stw81-oinfinity-envelopes-have-dimension-one-or-infinity
artifacts:
  - research/artifacts/stw81-fibrewise-oinfinity-colour-collapse-audit-2026-08-30.md
---

The fibrewise-to-global input is Hirshberg--Rordam--Winter,
[*C0(X)-algebras, stability and strongly self-absorbing C-star
algebras*](https://arxiv.org/abs/math/0610344), Theorem 4.6.  If `D` is a
K1-injective strongly self-absorbing algebra, `X` is finite-dimensional,
locally compact and metrizable, and `A` is a separable `C_0(X)`-algebra,
then `A` is `D`-stable exactly when all its fibres are `D`-stable.  This is
a theorem for arbitrary `C_0(X)`-algebras; continuity of the associated
field is not an assumption.

Take `D=O_infinity`.  It is K1-injective and strongly self-absorbing, so the
fibre hypothesis gives

```text
A tensor O_infinity isomorphic to A.                    (FAP1)
```

Bosa--Gabe--Sims--White,
[*The nuclear dimension of O-infinity-stable C-star
algebras*](https://arxiv.org/abs/1906.02066), gives
`dim_nuc(A)<=1` for separable nuclear `A`, proving `(FOC1)`.  If `A` is
nonzero, nuclear dimension zero would make it AF.  A nonzero AF algebra
cannot be O-infinity-stable, so the dimension is exactly one.

Now assume the nonzero fibres are simple.  For an ideal `J ideal A`, the
fibre of `A/J` at `x` is a quotient of `A_x`, hence is zero or `A_x`.  If a
commutative hereditary subalgebra `C subset A/J` were nonzero, some fibre
`C_x` would be nonzero.  It is a commutative hereditary subalgebra of the
simple O-infinity-stable algebra `A_x`.  A simple algebra with a nonzero
commutative hereditary subalgebra is elementary, whereas a nonzero
O-infinity-stable algebra is strongly purely infinite and not elementary.
This contradiction proves the shadow-free assertion.

For the mixed statement, the clopen decomposition gives

```text
A=A_el direct_sum A_inf.
```

The continuous-trace nuclear-dimension formula gives
`dim_nuc(A_el)=dim(X_el)<=1`.  Apply the preceding fibrewise absorption
argument to `A_inf` to obtain `dim_nuc(A_inf)<=1`; finite-direct-sum
permanence proves `(FOC2)`.  In a quotient, any commutative hereditary
shadow on the absorbing side is zero by the preceding argument.  On the
continuous-trace side it is Morita equivalent to a continuous-trace ideal
over a locally closed subspace of `X_el`, so its spectrum has dimension at
most one.
