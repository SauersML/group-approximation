---
rg: 2
id: stw77-properly-infinite-colored-centralizer-fusion
kind: claim
title: Properly infinite image data admits uniform finite-color centralizer fusion
---

For every `d,m` and `epsilon>0` there is `eta>0` with the following
property.  Let `phi:A->B` be a unital homomorphism, let
`a_1,...,a_m` be contractions, and suppose every nonzero positive element of
`phi(A)` is properly infinite in `B`.  If there are finite-dimensional
algebras `F_0,...,F_d`, a cpc map

```text
alpha:A -> direct_sum_(i=0)^d F_i
```

and cpc order-zero maps `beta_i:F_i->B` such that

```text
||phi(a_j)-sum_i beta_i alpha_i(a_j)|| < eta
```

for all `j`, then there are exact orthogonal isometries `s_1,s_2 in B` with

```text
max_(j,r) ||[s_r,phi(a_j)]|| < epsilon.
```

The uniformity of `eta` over the algebras and maps is part of the claim.

## Attempts

- For an internal finite-dimensional subalgebra of `phi(A)`, matrix-unit
  transport proves the assertion exactly; this is
  `stw77-af-range-maps-are-oinfty-stable`.
- Generic outgoing order-zero ranges are not internal.  Their support
  contractions need not lie in `phi(A)`, so the pointwise proper-infiniteness
  hypothesis does not apply to them.
- Domination does not repair this: by
  `proper-infinity-does-not-descend-to-color-supports`, even a positive
  contraction below a properly infinite unit can be finite.
- Splitting each color separately would still leave a fusion problem because
  different order-zero color ranges need not commute.  A successful proof
  needs isometries that centralize the **sum** of the colors without assigning
  proper infiniteness independently to their supports.
