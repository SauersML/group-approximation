---
rg: 2
id: kervaire-laudenbach-holds-for-linear-sofic-groups
kind: claim
title: The Kervaire--Laudenbach conjecture holds for groups that are linear sofic over some field
distinct_from:
  kervaire-laudenbach-holds-for-hyperlinear: that is the class of groups embedding in unitary Hilbert--Schmidt ultraproducts; this is the rank-metric class, which contains every sofic group and sits inside the weakly sofic groups, and is not known to contain or be contained in the hyperlinear class.
  kervaire-laudenbach-holds-for-mf: that is the operator-norm corona class; this is the rank-metric class.
  kervaire-laudenbach-nonsingular-conjecture: that is the conjecture for all groups; this is its restriction to linear sofic coefficient groups.
artifacts:
  - research/artifacts/ideas-nonhyperlinear-2026-09-13.md
---

**OPEN.** If `G` is `F`-linear sofic for some field `F` and `w` in
`G * <t>` has nonzero exponent sum in `t`, then
`G --> (G * <t>)/<<w>>` is injective.

The class: by `sofic-implies-linear-sofic-over-every-field` and
`linear-sofic-implies-weakly-sofic-over-every-field`,
`sofic <= F-linear sofic <= weakly sofic` for every field `F`.

The route `kl-for-linear-sofic-via-amplified-algebraic-roots` reduces this to
the matrix statement `amplified-algebraic-roots-for-nonsingular-equations`.
