---
rg: 2
id: at-op62-representation-lifts-proof
kind: route
title: Lift, average with the lazy Kazhdan operator, and read the corollary of the corner lemma
target: at-op62-holds-for-representation-lifts
requires:
  - kazhdan-almost-invariant-corner-near-invariant-projection
---

The inclusion `prod_U (rho_n(Gamma)' cap M_(d_n)) subseteq pi(Gamma)' cap M`
is levelwise.  Conversely, `u in pi(Gamma)' cap M` lifts to an
operator-norm bounded sequence `(u_n)` with
`|| [u_n, rho_n(s)] ||_(2,d_n) -> 0` along the ultrafilter for each `s`
in a finite Kazhdan generating set `S` (commutation in `M` with each
`pi(s)`).  The lazy averages of the ultraproduct corollary `(KA3)` of
`kazhdan-almost-invariant-corner-near-invariant-projection` produce
`X_n := P_inv(u_n) in rho_n(Gamma)' cap M_(d_n)`, contractions with

```text
|| X_n - u_n ||_(2,d_n) <= (1/kappa) max_(s in S) || [u_n, rho_n(s)] ||_(2,d_n) -> 0,
```

using that `Ad rho_n` is a genuine unitary representation of `Gamma` on
`HS(C^(d_n))` and `(S, kappa)` is a Kazhdan pair (invariant vectors of
`Ad rho_n` = the centralizer).  Hence `(X_n)` represents `u` and lies in
the coordinate-centralizer ultraproduct.
