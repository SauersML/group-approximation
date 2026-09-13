---
rg: 2
id: braid-proper-cat0-action-from-geometric-action
kind: route
title: A geometric action on a complete CAT(0) space is a proper action on a proper CAT(0) space
target: every-braid-group-acts-properly-on-a-proper-cat0-space
requires:
  - every-braid-group-is-cat0
---

If `B_n` acts properly and cocompactly by isometries on a complete CAT(0)
space `X`, the action is proper and `X` is a proper metric space. So
`every-braid-group-is-cat0` gives
`every-braid-group-acts-properly-on-a-proper-cat0-space`.

**Lemma.** Let a group `G` act by isometries on a complete geodesic space `X`,
properly (every `x` has `r_x > 0` such that
`F(x, r_x) = {g : g B(x, r_x) ∩ B(x, r_x) ≠ ∅}` is finite) and cocompactly
(`X = G K` for a compact `K`). Then `X` is proper.

*Proof.*

1. Uniform radius. Cover `K` by finitely many open balls `B(k_i, r_i / 2)`
   with `r_i = r_{k_i}`, and let `r = min_i r_i / 2`. Any `k` in `K` lies in some
   `B(k_i, r_i / 2)`, so `B(k, r) ⊆ B(k_i, r_i)` and `F(k, r) ⊆ F(k_i, r_i)` is
   finite.
2. Small balls meet finitely many translates of `K`. Let `ε = r / 4` and
   `x` in `X`; translating by an element of `G` we may assume `x` lies in `K`.
   Suppose infinitely many distinct `g_n` have `g_n K ∩ B(x, ε) ≠ ∅`. Pick `k_n`
   in `K` with `g_n k_n` in `B(x, ε)`, and pass to a subsequence with `k_n -> k`
   in `K` and `d(k_n, k) < ε` for all `n`. Then `d(g_n k, x) < 2ε`, so
   `d(g_n k, g_m k) < 4ε = r`, i.e. `g_m^{-1} g_n k` lies in `B(k, r)` and
   `g_m^{-1} g_n` lies in `F(k, r)`. Fixing `m`, every `g_n` lies in the finite set
   `g_m F(k, r)`: a contradiction.
3. So `B(x, ε)` lies in a finite union of translates of `K`, which is compact,
   and the closed ball of radius `ε / 2` about `x` is compact. Every point has
   a compact neighbourhood of the same radius, and a complete, locally compact
   length space is proper (Hopf–Rinow–Cohn-Vossen; Bridson–Haefliger I.3.7). ∎

The action of `B_n` on `X` is proper by hypothesis, so this is a proper
isometric action on a proper CAT(0) space.
