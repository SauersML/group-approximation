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
- For a field `K`, unique products give a leading-term argument.  If `x, y`
  are nonzero in `K[W]`, some element of `supp(x) supp(y)` has a unique
  expression, its coefficient in `xy` is a product of two nonzero scalars, and
  so `xy != 0`.
- Units are trivial.
  - A group with unique products has the *two* unique products property:
    whenever `|A| + |B| > 2`, at least two elements of `AB` have a unique
    expression.  This is Strojnowski, *A note on u.p. groups*, Comm. Algebra 8
    (1980), cited here from the reviewer's note and not re-read.
  - Now suppose `xy = 1` with `|supp(x)| + |supp(y)| > 2`.  Two elements of
    `supp(x) supp(y)` then keep nonzero coefficients in `xy`, but `1` has a
    single support element.  So both supports are singletons, and `x = c w`
    with `c` in `K^x` and `w` in `W`.
  - Kionke--Raimbault, arXiv:1411.6449v2, p. 1, state the conclusion:
    "if a group Γ has unique products, then it satisfies Kaplansky's unit
    conjecture."
- A domain is directly finite.  If `xy = 1`, then `yx` is an idempotent.  It is
  nonzero because `x (yx) y = 1`, so `yx (1 - yx) = 0` forces `yx = 1`.

The two cases are exhaustive.  ∎
