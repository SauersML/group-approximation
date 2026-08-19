---
rg: 2
id: atlas-three-word-permutation-countermodel-proof
kind: route
title: Replay the exact twelve-point three-word countermodel
target: atlas-three-word-permutation-countermodel
---

The artifact `experiments/atlas_three_word_permutation_countermodel.py` uses
only exact permutation arithmetic and exact `4 x 4` arithmetic over `F_2`.
It first verifies from the canonical atlas matrices that the three selected
words see a `C6` subgroup in chart one and an `S3` subgroup in chart two.

On twelve points it fixes two regular `C6` orbits and exhausts the
fixed-point-free involutions satisfying the two pair-cube relations.  Exactly
`72` choices survive the collision relation while the generated second-chart
subgroup has two six-point regular `S3` orbits.  For each survivor all three
selected words evaluate literally to the identity.

Direct-summing `1680*k` copies preserves every word identity and turns the
`C6` and `S3` restrictions into exactly the restrictions of
`Reg(A8) tensor I_k` to those support subgroups.  Hence the three squared
normalized-HS defects are all zero in dimension `20160*k` for every `k>=1`.
This contradicts any proposed positive lower bound `epsilon` in
`atlas-a4-three-word-amplified-gap`.
