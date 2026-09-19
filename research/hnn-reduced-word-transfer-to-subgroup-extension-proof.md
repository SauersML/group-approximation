---
rg: 2
id: hnn-reduced-word-transfer-to-subgroup-extension-proof
kind: route
title: The associated subgroup of the small extension is a comap, so reducedness transfers letter by letter
target: hnn-reduced-word-transfer-to-subgroup-extension
requires: []
artifacts:
  - GroupApproximation/Computability/BooneGroupTower.lean
---

## Direct proof, machine-checked

Three declarations, and the first is the whole idea.

`mem_toSubgroup_subOne_iff`: for a letter `a` *of `A`* and a unit `u : Z^x`,

    a in HNNExtension.toSubgroup (subOne A Asub) (subOne A Bsub) u
      <->  (a : G) in HNNExtension.toSubgroup Asub Bsub u,

because `subOne A Asub` is by definition `Asub.subgroupOf A`, a comap.  Both
cases of `Int.units_eq_one_or` are `Subgroup.mem_subgroupOf` after unfolding
`toSubgroup_one` / `toSubgroup_neg_one`.

`pushWord`: a `ReducedWord` over `A` maps to a `ReducedWord` over `G` by
applying the coercion to each letter.  Its `chain` field is the previous
statement applied inside `List.isChain_map` -- no induction on the number of
stable letters, and no pinching.

`smallLift_prod`: `smallLift phi hA (w.prod (goodEquiv phi hA)) = (pushWord
w).prod phi`, by `map_list_prod` and `List.map_congr_left`, with the letterwise
computation discharged by `HNNExtension.lift_t` and `lift_of`.

That is exactly the pair of items the consumer needs, and neither is an
induction.
