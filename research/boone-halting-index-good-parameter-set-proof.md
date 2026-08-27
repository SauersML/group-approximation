---
rg: 2
id: boone-halting-index-good-parameter-set-proof
kind: route
title: Intersect index sets, then apply the machine fact once
target: boone-halting-index-good-parameter-set
requires: [modular-machine-halting-invariance, boone-base-group-and-lemma-five, free-subbasis-subgroup-calculus]
artifacts:
  - GroupApproximation/Computability/BooneGroupMachineIndex.lean
---

## Why sufficient

Every subgroup in sight is a sub-basis subgroup of the free part `T`, so all
three prerequisites act at once and nothing else is needed.

**The intersections.**  `T_M` is `twSub (haltingSetZ)` and `G_{ab}^{MN}` is the
range of `emb a b M N`; intersecting them is `twSub_inf` (from the sub-basis
calculus, transported in the split-extension model) applied to the index sets,
plus Lemma 5 for the `T`-side bookkeeping.  This gives
`twSub_halting_inf_Gsub` and `Tsub_inf_Gsub_image` with no machine input.

**The parameter set.**  `haltParams a b = {(u,v) | Halts (a + uM, b + vM)}`.
Reading it through the target embedding instead of the source one changes the
configuration by exactly one machine step, so `haltParams_eq_right` and
`haltParams_eq_left` are `haltsZ_right_iff` and `haltsZ_left_iff` -- the second
prerequisite -- applied once each.  This is the only appeal to the machine in
the whole module.

**The images.**  `image_haltParams_src`, `image_haltParams_right` and
`image_haltParams_left` compute the images of `haltParams` under the two
embeddings as `H_M` intersected with the respective index class; the injective
index maps `embIdx` are from the third prerequisite via `range_indexMap`.
Combining gives the three `twSub_halting_inf_Gsub_*` statements.

## Not a restatement of any prerequisite

The machine fact is about configurations in `N x N` and mentions no group; the
base-group claim is about arbitrary sub-basis subgroups and mentions no
machine; the sub-basis calculus mentions neither.  The content here is that
*one and the same* parameter set describes both sides of a quadruple's
identification, which is what makes goodness available downstream.
