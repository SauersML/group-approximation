---
rg: 2
id: thompson-t-is-sofic
kind: claim
title: Thompson's group T is sofic
distinct_from:
  thompson-f-is-sofic: that is soficity of F, which this implies because F <= T; the converse is not known.
  thompson-v-is-sofic: that is soficity of V, which implies this because T <= V; the converse is not known.
  thompson-t-has-a-fixed-point-free-amenable-action: that is one sufficient condition for this claim through amenable actions; a refutation of it would say nothing against this claim.
---

**OPEN.** Thompson's group `T` embeds in the universal sofic group.

**Position in the graph.**
- It implies `thompson-f-is-sofic` (route `thompson-f-sofic-from-t-sofic`).
- It follows from `thompson-v-is-sofic` (route `thompson-t-sofic-from-v-sofic`) and from
  `thompson-t-has-a-fixed-point-free-amenable-action` (route
  `thompson-t-sofic-from-fixed-point-free-amenable-action`).
- The discrete Euler route to `lifted-thompson-t-is-a-t-menable` passes through the latter
  (route `thompson-t-fixed-point-free-amenable-action-from-euler-subgroup`). So any witness for
  `thompson-t-co-amenable-subgroup-kills-real-euler-class` proves this claim.

**Known obstructions to cheap witnesses.** Spatial truncations of the circle action never give a
sofic approximation (`thompson-t-orbits-carry-no-invariant-means`, item 1). `T` is simple, so it
has no nontrivial finite quotients. By `thompson-t-amenable-actions-are-free-off-fixed-points`,
item 1, amenable-action witnesses are automatically essentially free, and their stabilizers are
unconfined and fix no probability on dyadic arcs.
