---
rg: 2
id: boone-normal-closure-of-t-finitely-generated-proof
kind: route
title: Each stage adds exactly one generator, the stable letter
target: boone-normal-closure-of-t-finitely-generated
requires: [boone-base-group-and-lemma-five]
artifacts:
  - GroupApproximation/Computability/BooneGroupFinitePresentation.lean
---

## Why sufficient

Both halves, in `Computability/BooneGroupFinitePresentation`.

**The `G_{ab}^{MN}` half is a corollary of the prerequisite.**  `Gsub_fg`:
`Gsub_eq_closure` exhibits `G_{ab}^{MN}` as `⟨t(a,b), x^M, y^N⟩`, three
elements, so `Subgroup.fg_iff` applies directly.  Images stay finitely
generated (`Subgroup_FG_map`, the image of a generating set generates the
image), which is the form the tower needs since its associated subgroups are
`Gsub`s pushed along `ι`.

**The `⟨t⟩'` half is the one that could have failed**, and the reason it does
not is structural rather than computational.  `liftedSubgroup φ A` is by
definition `⟨of '' A, t⟩`, so if `A = ⟨X⟩` then
`liftedSubgroup φ A = ⟨of '' X, t⟩` --- `MonoidHom.map_closure` turns the image
of a closure into the closure of the image, and `Subgroup.closure_union` splits
the union.  That is `liftedSubgroup_fg`: **one stage costs one generator**.

`towerTSub_fg` is then the induction along the fold: the base is `⟨t⟩`, one
generator, and each identification adds its stable letter.  A machine's list is
finite, so the total is finite --- which is exactly why `⟨t⟩'` is finitely
generated in the tower while being free of infinite rank in the base group.

## Why the prerequisite is the base group claim

`Gsub_eq_closure` is the statement that the range of `emb` *is*
`⟨t(a,b), x^M, y^N⟩`, which is item S2b of the roadmap and is part of that
claim.  Without it one knows only that `Gsub` contains those three elements,
which gives no generating set at all.
