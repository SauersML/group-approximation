---
rg: 2
id: fp-torsion-presentations-have-nonpositive-p-deficiency-proof
kind: route
title: Positive p-deficiency gives linear mod-p homology growth, finite presentation makes that p-large, and p-large groups are not torsion
target: fp-torsion-presentations-have-nonpositive-p-deficiency
requires:
  - fpbs-power-p-deficiency-schreier-bound
  - fpbs-lackenby-derived-p-series-largeness
---

Let `G` be finitely presented with `c = def_p(G) > 0`.

1. **Derived `p`-series.** Put `D_0 = G` and `D_(i+1) = [D_i, D_i] D_i^p`.
   Each `D_i` is characteristic in `G`. `G` is finitely generated, so each
   quotient `D_i/D_(i+1)` is a finitely generated elementary abelian
   `p`-group, hence finite. So every `D_i` is a normal subgroup of `p`-power
   index in `G`.
2. **Linear growth.** By `fpbs-power-p-deficiency-schreier-bound`,
   `(d_p(D_i) - 1)/[G:D_i] >= c`, so `inf_i d_p(D_i)/[G:D_i] >= c > 0`.
3. **Largeness.** `G` is finitely presented, so
   `fpbs-lackenby-derived-p-series-largeness` makes `G` `p`-large. Some normal
   subgroup `N` of `p`-power index maps onto a nonabelian free group `F_2`.
4. **Not torsion.** Lift a free generator of `F_2` to an element `x in N`.
   Every power `x^k` with `k != 0` maps to a nontrivial element of `F_2`, so
   `x` has infinite order in `G`.

Hence a finitely presented torsion group has `def_p(G) <= 0`. A finite
presentation `(X,R)` of `G` is one of the presentations in the supremum, so
`|X| - 1 - sum_r p^(-nu_p(r)) <= 0`. ∎

This is the argument of `fpbs-power-p-deficiency-excludes-property-t-proof`,
with "finite index subgroup with infinite abelianization" replaced by
"element of infinite order". Here `G` itself must be finitely presented,
because torsion, unlike property (T), does not pass to finitely presented
covers.
