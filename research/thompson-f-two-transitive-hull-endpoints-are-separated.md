---
rg: 2
id: thompson-f-two-transitive-hull-endpoints-are-separated
kind: claim
title: In a 2-transitive action of Thompson's group F, the two hull endpoints are ultrametric in opposite senses and are strictly separated on every pair
distinct_from:
  thompson-f-two-transitive-hull-endpoints-are-rational: that claim defines the hull endpoints xi <= eta, shows they are rational, equivariant and fixed by swaps; this claim proves the triangle rules for eta and xi and the strict inequality xi < eta
  thompson-f-two-transitive-actions-satisfy-grid-condition: that claim compares left and right half orbits at one point x; this claim compares the hull endpoints of the three pairs of a triple of points of the abstract set
---

Let `F` act on a set `Ω`, `|Ω| ≥ 3`, transitively on ordered pairs of distinct
points, and let `η(ω,ω')` and `ξ(ω,ω')` be the hull endpoints of
`thompson-f-two-transitive-hull-endpoints-are-rational`:
`η = inf{x : ω' ∈ F_x^- ω}` and `ξ = sup{x : ω' ∈ F_x^+ ω}`. Then:

1. (Triangle rules.) For distinct `ω_1, ω_2, ω_3`,
   `η(ω_1,ω_3) ≤ max(η(ω_1,ω_2), η(ω_2,ω_3))` and
   `ξ(ω_1,ω_3) ≥ min(ξ(ω_1,ω_2), ξ(ω_2,ω_3))`.
   So in every triple the largest `η`-value is attained at least twice, and the
   smallest `ξ`-value is attained at least twice.
2. (Separation.) `ξ(ω,ω') < η(ω,ω')` for every pair `ω ≠ ω'`.

So `η` is an `F`-equivariant ultrametric on `Ω` with values in `(0,1)`, `ξ` is
an `F`-equivariant ultrametric for the reversed order, and the hull
`[ξ(ω,ω'), η(ω,ω')]` of every pair is a nondegenerate interval.

**What this kills.** Every candidate model in which some pair of points
"disagrees at a single point" `t` of `(0,1)`, i.e. `ω'` is reached from `ω` by
elements supported in `[0,x]` for all `x > t` and by elements supported in
`[x,1]` for all `x < t`. Examples are the models built by changing a label or a
germ class at one point of an orbit `Θ` while keeping everything else. By
item 2, no 2-transitive action contains such a pair.

Scope: proved by a swarm agent on 2026-09-17; no independent review. No novelty
is claimed. An ultrametric-type inequality for hulls was already noted in the
Attempts of `thompson-f-has-no-faithful-2-transitive-action`. What is added here
is the pair of opposite triangle rules and the strict separation. The proof uses only item 1 of the hull-endpoint claim and the fact
that `F` fixes no point of `(0,1)`.

**Proof:** `thompson-f-two-transitive-hull-endpoints-separated-proof`.
