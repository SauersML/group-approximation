---
rg: 2
id: thompson-t-has-a-fixed-point-free-amenable-action
kind: claim
title: Some Thompson T-set without global fixed points carries a T-invariant mean
distinct_from:
  thompson-v-has-a-fixed-point-free-amenable-action: that is the same question for V; neither is known to imply the other, since co-amenability does not pass from T to V or back.
  thompson-t-is-sofic: that is soficity of T; this is one sufficient condition for it, and a refutation of this would say nothing against soficity.
  thompson-t-amenable-actions-are-free-off-fixed-points: that proves what every invariant mean on a T-set must look like; this asks whether one off the global fixed set exists at all.
  thompson-t-co-amenable-subgroup-kills-real-euler-class: that asks for a proper co-amenable subgroup with an extra cohomological property; this drops the cohomology and allows several orbits.
  thompson-t-orbits-carry-no-invariant-means: that excludes the circle orbits and their configuration spaces; this asks about arbitrary T-sets.
---

**OPEN.** Let `T` be Thompson's circle group with finite symmetric generating set `S`. Prove that
some `T`-set `Ω` with no global fixed point carries a `T`-invariant mean on `ℓ∞(Ω)`.

**Equivalent forms.** By item 2 of `thompson-t-amenable-actions-are-free-off-fixed-points`, this is
equivalent to each of:
- `T` has a mean-free (essentially free) amenable action;
- `inf { φ_S(T/H) : H < T proper } = 0`.

A proper co-amenable subgroup `H < T` suffices, with `Ω = T/H`.

**Why it matters.**
- It implies `thompson-t-is-sofic` and so `thompson-f-is-sofic`.
- It is implied by `thompson-t-co-amenable-subgroup-kills-real-euler-class` (route
  `thompson-t-fixed-point-free-amenable-action-from-euler-subgroup`). So it is a prerequisite that
  can fail on its own for the discrete Euler route to `lifted-thompson-t-is-a-t-menable`: if every
  proper subgroup of `T` has `φ_S(T/H)` bounded below uniformly, that route is dead.
- Amenability of `F` does not give it. `F`, the stabilizer of `0`, fixes `δ_0`, so it is never
  co-amenable in `T`. No link to the `F`-amenability lane is known.

**Shape of a witness** (items 1, 3 and 4 of `thompson-t-amenable-actions-are-free-off-fixed-points`).
Almost every stabilizer is proper, misses each fixed finite subset of `T \ {e}`, is not confined,
and fixes no finitely additive probability on dyadic arcs. In particular it is nonamenable, has no
finite orbit on `S^1`, and is none of `F`, the rotation subgroup or their conjugates.
