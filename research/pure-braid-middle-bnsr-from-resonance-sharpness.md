---
rg: 2
id: pure-braid-middle-bnsr-from-resonance-sharpness
kind: route
title: Resonance sharpness plus explicit higher resonance varieties give the intermediate invariants
target: pure-braid-middle-bnsr-invariants-computed
requires:
  - pure-braid-bnsr-complements-are-real-resonance-varieties
  - braid-arrangement-higher-resonance-varieties-computed
---

If `Sigma^m(P_n)` is the complement of `S(R^{<=m}(P_n; R))`
(`pure-braid-bnsr-complements-are-real-resonance-varieties`), and each `R^i`
with `i <= m` is an explicit finite union of linear subspaces
(`braid-arrangement-higher-resonance-varieties-computed`), then the complement
of `Sigma^m(P_n)` is the sphere of that explicit union, which is the
description asked for. The subspaces are rational: the resonance varieties of
arrangements are unions of rationally defined linear subspaces, because they
are tangent cones of the characteristic varieties, which are unions of
subtori (Suciu arXiv:2010.07499, Section 13.1 and Theorem 13.3).
