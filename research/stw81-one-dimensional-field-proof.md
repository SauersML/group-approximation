---
rg: 2
id: stw81-one-dimensional-field-proof
kind: route
title: Split the fibre regimes and absorb O-infinity locally over the finite-dimensional base
target: stw81-one-dim-elementary-oinfty-fields-have-dim-one
requires: []
artifacts:
  - research/artifacts/stw81-one-dimensional-field-audit-2026-08-30.md
---

Let `X_el` and `X_inf` denote the elementary-fibre and
O-infinity-stable-fibre loci.  Local triviality makes fibre isomorphism
type locally constant, so both loci are open.  They are complementary by
hypothesis and therefore clopen.  Consequently

`A=A_el direct_sum A_inf`.

The locally trivial elementary field `A_el` is continuous trace and has
spectrum `X_el`.  Winter--Zacharias' continuous-trace calculation gives

`dim_nuc(A_el)=dim(X_el)<=1`.

Every fibre of `A_inf` is O-infinity-stable.  The Cuntz algebra
`O_infinity` is K1-injective and strongly self-absorbing, so
Hirshberg--Rordam--Winter, Theorem 4.6, applies to the separable
`C_0(X_inf)`-algebra over the finite-dimensional locally compact
metrizable space `X_inf`.  It gives

`A_inf tensor O_infinity ~= A_inf`.

Since `A_inf` is separable and nuclear, the
Bosa--Gabe--Sims--White theorem gives `dim_nuc(A_inf)<=1`.  Nuclear
dimension of a finite direct sum is the maximum, proving
`dim_nuc(A)<=1`.

For the shadow assertion, let `C` be a commutative hereditary subalgebra
of a quotient of `A`, and let `J` be the ideal it generates.  Then `C` is
full hereditary in `J`, so `C` and `J` are strongly Morita equivalent;
in particular `J` is type I and `Prim(C)~=Prim(J)`.  The quotient and `J`
respect the clopen decomposition.  On the O-infinity-stable side, any
nonzero ideal has an O-infinity-stable simple fibre as a quotient, so it
cannot be type I.  Hence `J` is supported on the elementary side.  There
it is a continuous-trace subquotient over a locally closed subset of
`X_el`, whose covering dimension is at most one.  Therefore
`dim Prim(C)<=1`.
