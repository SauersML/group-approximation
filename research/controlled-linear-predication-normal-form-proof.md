---
rg: 2
id: controlled-linear-predication-normal-form-proof
kind: route
title: Orthogonal branch projections give exact gated involutions
target: controlled-linear-predication-normal-form
requires: []
artifacts:
  - research/artifacts/compiler-lowering-hyperlinear-2026-08-18.md
---

Since `P_a` commutes with `U_i` and `U_i^2=1`,

```text
(P_a U_i + 1-P_a)^2 = P_a + 1-P_a = 1,
```

and the operator is self-adjoint. Orthogonality of the `P_a` gives, on the
`P_a` summand, exactly one factor `G_(a,i)` acting as `U_i` and every other
branch factor acting as the identity; hence `prod_a G_(a,i)=U_i`.

For one fixed branch, commutation of the relevant `U_i` and the fact that each
commutes with `P_a` lets the product split across the two orthogonal corners:

```text
prod_(i in I_a) G_(a,i)
 = P_a prod_(i in I_a) U_i + (1-P_a).
```

The controlled equation replaces the first term by `(-1)^b P_a`. For `b=0`
this is `1`, and for `b=1` it is `1-2P_a=Z_a`; equivalently it is `Z_a^b`.
Every step reverses, proving equivalence.
