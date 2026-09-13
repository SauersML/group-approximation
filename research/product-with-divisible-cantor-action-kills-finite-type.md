---
rg: 2
id: product-with-divisible-cantor-action-kills-finite-type
kind: claim
title: Multiplying an action whose doubled unit class is properly infinite by any divisible Cantor action makes the unit class properly infinite
distinct_from:
  topologically-free-minimal-cantor-action-with-finite-clopen-type: that constructs a finite unit class; this shows product constructions destroy it, so they cannot supply topologically free Z-stable variants that keep it.
---

**Theorem.**  Let `Gamma` act on a Cantor space `X` with `2[1_X]` properly
infinite in `S(X, Gamma)`.  Let `H` act on a Cantor space `Y`, and suppose
`Y` has a clopen partition `V, V', W, W', W''` with `V ~ V'` and
`W ~ W' ~ W''` equidecomposable in `S(Y, H)` (so `[1_Y] = 2a + 3b`; `W` may be
empty).  Then `[1_{X x Y}]` is properly infinite in `S(X x Y, Gamma x H)`, so
the unit of `C(X x Y) rtimes_r (Gamma x H) = (C(X) rtimes_r Gamma) tensor_min
(C(Y) rtimes_r H)` is properly infinite.

The hypothesis on `Y` holds for every minimal action of `Z` on a Cantor space
(Kakutani--Rokhlin towers of height at least 2, split into pairs and triples
of consecutive levels), hence for any `H` containing an element acting
minimally.

**Consequence.**  If both factors are minimal and topologically free, so is
the product, and it has no invariant probability measure when `X` has none.
But the finite class is gone.  Boldrini--Prasad's Z-stable variants
(arXiv:2607.01896, Theorem 7.4) use an acting group whose second factor acts
trivially, which is not topologically free; this theorem shows that no product
with a divisible Cantor action can make them topologically free while keeping
`[1]` finite.

Status: proved in the route below, unreviewed.
