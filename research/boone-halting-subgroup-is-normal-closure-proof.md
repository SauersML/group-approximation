---
rg: 2
id: boone-halting-subgroup-is-normal-closure-proof
kind: route
title: Both inclusions between the halting lift and the normal closure of t
target: boone-halting-subgroup-is-normal-closure
requires: [boone-tower-good-subgroup-transport, modular-machine-halting-invariance]
artifacts:
  - GroupApproximation/Computability/BooneGroupGoodness.lean
  - GroupApproximation/Computability/BooneGroupTower.lean
---

## Why sufficient

`BooneGroupGoodness.towerSub_halting_eq_towerTSub`:

    towerSub (twSub H_M) (machineIdentifications mm hM)
      = towerTSub (machineIdentifications mm hM),

which is Simpson's Lemma 7 in the tower's own language -- the lift of the
halting subgroup through the fold is the lift of `⟨t⟩`.  It is proved by
`le_antisymm`, and the two inclusions are where the prerequisites go.

**`≤`.**  `towerSub_le_of_mem` reduces to a membership check at each level, and
`twSub_halting_le_comap` is that check: a basis element of the halting set stays
in the comap of the next level's subgroup.  This is the machine fact of
[[modular-machine-halting-invariance]] read through the stable letter, whose
step is `stable_conj_emb_right` / `_left` -- the stable letter attached to a
quadruple carries the source embedding onto the target, which is exactly
Simpson's displayed computation `rᵢ⁻¹ t(α,β) rᵢ = t(α₁,β₁)`.

**`≥`.**  `towerTSub_le_towerSub_halting` runs the induction the other way, and
`hasLetters_towerTSub` is the structural fact that the lift of `⟨t⟩` really does
contain the stable letters at every level.

Goodness -- [[boone-tower-good-subgroup-transport]] -- is what makes both
inductions stay inside the base group at each stage; without it the lift would
acquire elements the next level cannot see.

## Not a restatement

The prerequisites say the halting subgroup is *good* at every quadruple and
that halting is invariant under one machine step; neither identifies the
subgroup that the lift generates. The identification is the content, and it is
the step Simpson proves by induction on the length of a halting computation.
