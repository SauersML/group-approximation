---
rg: 2
id: jacobson-linear-head-gauge-and-ts-augmentation
kind: claim
title: Characteristic-two natural-head linear gauges split a tail carrier and the TS cell forbids augmentation preservation
distinct_from:
  jacobson-ts-cell-excludes-monomial-natural-head-models: that uses support of monomial matrices; this gives a first-braid normal form for arbitrary linear involutions and excludes augmentation-preserving nonmonomial tail actions and involutions.
  jacobson-ts-cell-is-independent-after-first-raw-commutation: that evaluates the TS word in one seven-ray quotient; this imposes exact restrictions on a whole class of characteristic-two natural-head linear models.
artifacts:
  - research/artifacts/jacobson-natural-head-linear-gauge-and-augmentation-2026-09-08.md
---

Let `k` be a field of characteristic two and let `M!=0,Y` be based
algebraic vector spaces, of finite or infinite dimension. Represent
`GL_3(F_2)_Q x GL_3(F_2)_P` on
`V=(k^3 tensor M) direct-sum Y`, with the natural head action on the
first factor and trivial head action on `Y`. Let `H` be an arbitrary
linear involution commuting with `K=GL(<e_1,e_3>)_Q`.

If `(H pi(w_23,w_23))^3=I`, then the `V_2->V_2` block of `H`
vanishes. There is a split injection `q:M->Y` such that `H` exchanges
`V_2=e_2 tensor M` with `q(M)`. The tail involution `w_23,P`
preserves both `q(M)` and a complementary subspace. The artifact gives
the complete necessary and sufficient block equations for this first braid.

Independently of either braid, suppose the tail matrices and `H`
preserve the functional summing all basis coefficients. Put

```text
c=(I+E_13)_P,
z=(I+E_23)_Q (I+E_23)_P,
k_0=(I+E_31)_Q (I+E_31)_P.
```

Then the TS word `W=[[H c H,k_0],H z H] z` is nonidentity.
This conclusion permits nonmonomial tail matrices and nonmonomial `H`.
In particular, over `F_2` with permutation tail, `W=I` requires an
even-support column in `H`.

These are restrictions on the stated characteristic-two linear model.
They assert no obstruction for arbitrary complex unitary representations,
no positive norm gap, and no MF or non-MF conclusion for `Gamma_2`.
