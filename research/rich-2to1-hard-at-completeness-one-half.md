---
rg: 2
id: rich-2to1-hard-at-completeness-one-half
kind: claim
title: For every eps it is NP-hard to tell fully rich 2-to-1 games of value >= (1-eps)/2 from value <= eps
distinct_from:
  rich-2to1-games-conjecture: that asks completeness 1-eps on rich instances; this is the proved gap at completeness (1-eps)/2, so richness itself costs nothing at the one-half wall.
  unique-games-hard-at-completeness-one-half: that is the unique games gap at completeness one half; this is the fully rich 2-to-1 gap, obtained from the imperfect-completeness 2-to-1 theorem by an arbitrary orientation lift and the BKM right merge, losing a factor 2 only in soundness.
  two-to-two-games-theorem: that gives near-1 2-to-1 hardness on linear F_lin-type pairings, far from rich; this gives rich pairings at completeness one half.
  perfect-completeness-rich-2to1-tractable-skeletons-are-in-p: that kills right merges at completeness 1; this uses a right merge at completeness one half, where that kill is silent.
artifacts:
  - experiments/orientation-lift-2026-09-17/check_orientation_lift.py
---

**ESTABLISHED.** For every `eps > 0` there is a constant `k = k(eps)` such
that `Gap-Rich-2-to-1[2k]((1-eps)/2, eps)` is NP-hard. The instances are weighted
bipartite 2-to-1 games with left alphabet `[2k]` and right alphabet `[k]`. At every
left vertex a weighted random incident edge induces the uniform distribution on
all perfect pairings of `[2k]` (BKM Definition 5, with edge weights read as
multiplicities).

**Meaning.** The richness condition is not what separates the proved theorems
from the Rich 2-to-1 Conjecture. At completeness one half it is free: lift a
proved 2-to-1 instance by an arbitrary orientation and right-merge it. What the conjecture adds
is completeness above one half. By `orientation-lifts-sandwich-2to1-game-values`,
that is the completeness of a branch selector, not a property of the pairing law.

**Proof in one line.** Lift the imperfect-completeness 2-to-1 instances by any
orientation, then apply the BKM right merge. The values move in the windows
`[1/2, 1]` and `[1, 2]`.

This is not a new hardness phenomenon. It is a composition of imported results
and the elementary lift bound, recorded because the target node says "the
whole difficulty is concentrated in supplying richness". Read at the one-half
wall, that sentence is false.

DERIVATION rich-2to1-hard-at-completeness-one-half-proof
