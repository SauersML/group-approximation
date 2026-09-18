---
rg: 2
id: kazhdan-nv-measured-minimal-sets-via-slope-principality
kind: route
title: Kazhdan minimal sets are slope-principal, and slope-principal minimal sets of subgroups of nV are measured
target: minimal-sets-of-kazhdan-subgroups-of-nv-carry-invariant-measures
requires:
  - minimal-sets-of-kazhdan-subgroups-of-nv-are-slope-principal
  - slope-principal-minimal-sets-of-nv-subgroups-carry-measures
---

1. Let `K <= nV` have property (T), and let `Z ⊆ C^n` be a minimal closed `K`-invariant
   set.
2. By `minimal-sets-of-kazhdan-subgroups-of-nv-are-slope-principal`, every `g ∈ K`
   fixing a point `z ∈ Z` has `s(g,z) = 0`. So `Z` is slope-principal for `K`.
3. By `slope-principal-minimal-sets-of-nv-subgroups-carry-measures`, applied with
   `G = K`, `Z` carries a `K`-invariant probability measure. ∎

**Independence of the halves.**
- The second prerequisite assumes no property (T), so it can fail on a non-Kazhdan
  subgroup of `nV` without affecting the target.
- The first prerequisite is implied by the target and holds for finite `K`. It fails
  exactly when some infinite Kazhdan `K` has a fixed point with nonzero slope, of
  compressing or saddle type, on a minimal set.
- Every use of (T) is pushed into the germ statement. The measure statement becomes a
  question about the slope cocycle on a principal groupoid with integer heights along
  orbits.
- By `nv-point-germ-groups-embed-in-zn-by-slope`, principality also excludes canonical
  self-compressions of bricks meeting `Z`. This is the only piece of the paradoxical
  decompositions of ping-pong type that the slope data sees directly.
