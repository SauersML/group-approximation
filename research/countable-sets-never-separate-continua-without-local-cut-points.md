---
rg: 2
id: countable-sets-never-separate-continua-without-local-cut-points
kind: claim
title: No countable closed set separates a Peano continuum without local cut points; so for every one-ended hyperbolic group that is not virtually Fuchsian and does not split over a two-ended subgroup (every infinite Kazhdan hyperbolic group, every random group at density below 1/2), the shear frontiers of loxodromic elements are uncountable
requires:
  - busemann-frontiers-separate-the-boundary
distinct_from:
  busemann-frontiers-separate-the-boundary: that proves the shear frontier separates the boundary and needs the topological input (T0), recalled only for spheres; this proves (T0) for all Peano continua without local cut points and applies it to Kazhdan and random groups.
---

**ESTABLISHED** (lane proof, bh-finf-hyp, 2026-09-19; elementary point-set topology; not reviewed). The statement is
probably classical (in the style of Whyburn's *Analytic Topology*). No priority is claimed, and the literature was
not searched beyond two web queries.

## Lemma

Let `X` be a Peano continuum (a locally connected metric continuum) with no local cut points. That is, for every
connected open `W` and every `p ∈ W`, the set `W ∖ {p}` is connected. Then `X ∖ C` is connected for every countable
closed `C ⊆ X`.

## Proof

- **Setup.** Suppose `X ∖ C = U ⊔ V` with `U`, `V` nonempty and open.
- **`X = cl U ∪ cl V`.** A point of `C` outside `cl U ∪ cl V` would have an open neighbourhood inside `C`. That is
  impossible: nonempty open sets of a nondegenerate Peano continuum contain nondegenerate connected open sets, so
  they are uncountable.
- **The common boundary.** Since `X` is connected, `K = cl U ∩ cl V` is nonempty. It is contained in `C`, so it is
  a countable compact set, and it has an isolated point `p` (Baire).
- **The neighbourhood.** Choose a connected open `W ∋ p` with `W ∩ K = {p}`, using local connectedness.
- **The contradiction.** `W ∖ {p} = A ⊔ B`, with `A = (W∖{p}) ∩ cl U` and `B = (W∖{p}) ∩ cl V`.
  - Both are relatively closed.
  - They are disjoint, since `W ∩ K = {p}`.
  - They cover `W ∖ {p}`, since `X = cl U ∪ cl V`.
  - Both are nonempty, since `p ∈ cl U ∩ cl V` and `W` is open.

  So `W ∖ {p}` is disconnected, and `p` is a local cut point, a contradiction. ∎

## Application to hyperbolic groups

- **Input.** For a one-ended hyperbolic `Γ`, `∂Γ` is a Peano continuum (Bestvina–Mess; Bowditch; Swarup).
- **Local cut points.** By Bowditch, `∂Γ` has a local cut point iff `Γ` splits over a two-ended subgroup or is
  virtually Fuchsian (recalled).
- **Kazhdan groups.** An infinite Kazhdan hyperbolic group has property (FA), so it has no splitting at all. It is
  one-ended, and it is not virtually Fuchsian. So `∂Γ` has no local cut points, and the Lemma applies.
- **Random groups.** Random groups at density `< 1/2` do not split (Dahmani–Guirardel–Przytycki). Their Menger
  boundary has no local cut points.

**Consequence.** For all these groups, (T0) of `busemann-frontiers-separate-the-boundary` holds. So every
loxodromic `g` has an **uncountable shear frontier `F`**, for `k` large.

**The only remaining step toward "BBMZ hosts of Kazhdan hyperbolic groups are unbounded" (Conjecture U)** is
persistence: that `g` is singular over the frontier. It is proved for reflections only.

## Lesson for general BH

The separation topology that decides whether germ-extension finiteness can work is exactly Bowditch's
local-cut-point topology. Groups whose boundaries have no local cut points, which include every Kazhdan hyperbolic
group, have uncountable shear frontiers. For them the bounded theory is expected to be unavailable, and no
dimension count is needed to see it.
