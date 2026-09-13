---
rg: 2
id: fg-rf-bounded-exponent-groups-are-finite-proof
kind: route
title: Finite quotients have bounded order by the restricted Burnside theorem, and residual finiteness separates any finite set in one finite quotient
target: fg-rf-bounded-exponent-groups-are-finite
requires:
  - restricted-burnside-finiteness
---

We may take `m >= 2` and `N >= 2`: if needed, add a trivial generator or
enlarge the exponent. By `restricted-burnside-finiteness` there are, up to
isomorphism, finitely many finite `m`-generated groups of exponent dividing
`N`. Let `M` be the largest of their orders.

Every finite quotient `Q` of `G` is `m`-generated with exponent dividing `N`,
so `|Q| <= M`.

Suppose `G` has `M + 1` distinct elements `g_0, ..., g_M`. For each pair
`i < j`, residual finiteness gives a finite-index normal subgroup `K_(ij)`
with `g_i g_j^(-1)` not in `K_(ij)`. The intersection `K` of these finitely
many subgroups is normal of finite index. The `g_i` stay distinct in `G/K`, so
`|G/K| >= M + 1 > M`. That contradicts the bound. Hence `|G| <= M`. ∎
