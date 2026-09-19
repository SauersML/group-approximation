---
rg: 2
id: slope-principal-measures-by-dimension-split
kind: route
title: Split by dimension: at n equal to one slope-principality forces every element to be locally of finite order near the minimal set, and the n at least two case is the remaining branch
target: slope-principal-minimal-sets-of-nv-subgroups-carry-measures
requires:
  - slope-principal-sets-of-v-are-locally-of-finite-order
  - locally-torsion-subgroups-of-v-have-measured-minimal-sets
  - slope-principal-minimal-sets-carry-measures-for-n-at-least-2
---

Let `G <= nV` and let `Z ⊆ C^n` be a minimal closed `G`-invariant slope-principal set.

1. If `n = 1`, then by Theorem A of `slope-principal-sets-of-v-are-locally-of-finite-order`
   every `g ∈ G` has `q >= 1` and a clopen `W ⊇ Z` with `g^q|_W = id`. That is exactly the
   hypothesis of `locally-torsion-subgroups-of-v-have-measured-minimal-sets`, which then
   gives a `G`-invariant probability measure on `Z`.
2. If `n >= 2`, this is `slope-principal-minimal-sets-carry-measures-for-n-at-least-2`. ∎

**Why the split is not a renaming.**

- The two branches have different content, not different wording. At `n = 1` the slope
  hypothesis is equivalent to a torsion hypothesis on the germs, and the remaining question
  is Burnside-type: an infinite finitely generated torsion group of germs of `V`-elements
  acting without an invariant measure. At `n >= 2` that equivalence is false, by Theorem B
  of the same node (Brin's baker map on the natural extension of an aperiodic minimal
  subshift), so the `n >= 2` branch must handle elements with no periodic points in `Z`,
  where the slope hypothesis says nothing.

**Status of the first prerequisite (2026-09-18).**
`slope-principal-sets-of-v-are-locally-of-finite-order` was demoted to OPEN at landing:
two of three referee lenses refuted it at Theorem B's `b`-invariance step (corrected
since, uncertified). This route therefore does not fire, which changes nothing about the
target, since both other prerequisites are OPEN as well. Step 1 uses only Theorem A,
which all three lenses found sound.
- Each branch can fail on its own: a non-amenable Burnside germ group in `V` would refute
  the first without touching the second, and a baker-type measure-free minimal set in `2V`
  would refute the second without touching the first.
