---
rg: 2
id: thompson-products-have-vanishing-zg-cohomology
kind: claim
title: "F x H has vanishing group-ring cohomology for every group H of type FP_infinity; in particular F x Z and F x F do"
distinct_from:
  thompson-f-has-vanishing-zg-cohomology: that is the Brown–Geoghegan theorem for F itself; this is its extension to direct products of F with any group of type FP_∞, by the Künneth formula.
---

**ESTABLISHED** through `thompson-products-have-vanishing-zg-cohomology-proof`.

Let F be Thompson's group F and let H be a group admitting a free resolution of
`Z` over `ZH` of finite type (for instance `H = Z` or `H = F`). Then

```text
H^n(F × H; Z[F × H]) = 0     for all n ≥ 0.
```

In particular `H^*(F × Z; Z[F × Z]) = 0` and `H^*(F × F; Z[F × F]) = 0`.

**Fence for Zaremsky Problem 2.4.** The group-ring cohomology of F, `F × Z` and
`F × F` vanishes identically, so this invariant cannot separate F from `F × Z`
(part (a)) or from `F × F` (part (b)), and it gives no obstruction to F × Z or
F × F being a quasi-retract of F (parts (d), (e)).
