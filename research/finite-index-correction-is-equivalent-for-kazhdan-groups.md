---
rg: 2
id: finite-index-correction-is-equivalent-for-kazhdan-groups
kind: claim
title: Correctability of Kazhdan microstates is equivalent on every fixed finite-index subgroup
distinct_from:
  subgroup-exact-outliers-do-not-exist: that proves the nontrivial induction direction from one near-exact subgroup restriction; this packages it with restriction and identifies the nested-congruence no-go.
  sl3z-regular-microstates-are-congruence-correctable: that asks whether the regular microstates are correctable at all; this proves that passing to a fixed congruence subgroup neither weakens nor strengthens that question.
  sl3-near-exact-leaks-live-in-the-two-primary-tower: that classifies the levels of an already available exact correction; this concerns existence of a correction before any level is available.
---

Let `G` be finitely presented with property `(T)` and let `N<=G` have fixed
finite index.  For any sequence of finite-dimensional normalized-HS
almost representations `sigma_j` of `G`, the following are equivalent:

1. `sigma_j` is flexibly close on a fixed generating set of `G` to exact
   finite-dimensional representations of `G`;
2. `sigma_j|_N` is flexibly close on a fixed generating set of `N` to exact
   finite-dimensional representations of `N`.

The implication `1=>2` is word telescoping.  The implication `2=>1` is the
induction-and-range-projection theorem
`subgroup-exact-outliers-do-not-exist`.  A flexible correction in dimension
`d_j+o(d_j)` may first be transported to a common stabilization: on the
common `1-o(1)` corner it gives the same-dimensional near-exact input of
that theorem, and the unmatched corner contributes only `o(1)` normalized
HS error.  All losses depend on the fixed index, fixed section words and a
Kazhdan pair, not on dimension.

Consequently, for any fixed nested family of finite-index subgroups

```text
G >= N_1 >= N_2 >= ...,
```

a noncorrectable microstate sequence for `G` restricts to a noncorrectable
sequence on **every fixed** `N_a`.  In particular, for
`G=SL_3(Z)`, the congruence subgroup property cannot force a good fixed
principal-congruence level: if it did, the induction theorem would already
correct the ambient tuple.  Conversely, any hypothetical ambient outlier
automatically furnishes a compatible inexact-on-every-fixed-level enemy by
restriction.  This does not construct an outlier and does not rule one out;
it proves that nested CSP localization is exactly equivalent to the original
regular-sector correction problem, rather than a route around it.
