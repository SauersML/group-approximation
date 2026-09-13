---
rg: 2
id: non-rf-hyperbolic-group-or-unique-product-nonsofic-group-proof
kind: route
title: Split on residual finiteness of the hyperbolic Leavitt cover
target: non-rf-hyperbolic-group-or-unique-product-nonsofic-group
requires: [hyperbolic-kazhdan-cover-of-leavitt-unit-group, hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup, rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group]
---

Let `1 -> N -> G -> R^x -> 1` be the cover of
`hyperbolic-kazhdan-cover-of-leavitt-unit-group`.  `G` is word-hyperbolic,
torsion-free and Kazhdan.

By `hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup`, applied to this
`G`, there are Kazhdan subgroups `N <= Gamma_hat <= G_hat <= G` with `Gamma_hat`
infranormal and not normal in `G_hat`.  They are the preimages of the nine-leaf
Leavitt pair under the covering map.

**Case 1: `G` is not residually finite.**  Then `G` is a word-hyperbolic group
that is not residually finite.

**Case 2: `G` is residually finite.**  Apply
`rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group` with `E = G_hat` and
`Gamma = Gamma_hat`.

- It gives a normal subgroup `G_k` of finite index in `G` with unique products.
- Put `E_k = G_hat cap G_k` and `Gamma_k = Gamma_hat cap G_k`.
- `W = (direct_sum_(E_k/Gamma_k) Z) x| E_k` has unique products and is not
  sofic.
- `W` is finitely generated: `E_k` has finite index in the finitely generated
  group `G_hat`, and `E_k` permutes the lamps transitively, so one lamp
  generates `L` as an `E_k`-module.
- `W` is torsion-free, since it has unique products.
- For a field `K`, unique products give a leading-term argument: a product
  `xy` of nonzero elements of `K[W]` has a uniquely expressed support element,
  so `xy != 0`.  The same argument shows that units are trivial.
- A domain is directly finite.  If `xy = 1`, then `yx` is an idempotent.  It is
  nonzero because `x (yx) y = 1`, so `yx (1 - yx) = 0` forces `yx = 1`.

The two cases are exhaustive.  ∎
