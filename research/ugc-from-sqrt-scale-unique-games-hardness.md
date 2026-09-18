---
rg: 2
id: ugc-from-sqrt-scale-unique-games-hardness
kind: route
title: Amplify sqrt-scale unique games hardness to UGC by constant-round Dinur--Steurer repetition
target: unique-games-conjecture
requires: [sqrt-scale-unique-games-hardness, sqrt-scale-unique-games-hardness-is-equivalent-to-ugc]
---

Immediate. `sqrt-scale-unique-games-hardness-is-equivalent-to-ugc` (Step 2 of
its proof) shows that the OPEN premise `sqrt-scale-unique-games-hardness`
implies `unique-games-conjecture`. The premise asks for the gap
`1 - eta` versus `1 - C sqrt(eta)` for every `C`.

This route is **two-way**, unlike `ugc-from-small-set-expansion-hypothesis`.
Step 3 of the same proof shows that UGC implies the premise. So the premise
fails exactly when UGC fails, and it is a reformulation at a different
quantifier level rather than a stronger hypothesis.

What a proof of the premise must supply, for each `C`:

* a reduction whose completeness deficit is `eta`;
* a soundness deficit of at least `C sqrt(eta)` at some scale `eta <= 1/C^2`;
* an alphabet of size at least `exp(C^2/(4A^2))`
  (`sqrt-scale-ug-hardness-costs-alphabet-exp-c-squared`).

Soundness deficits of order `o(sqrt(eta))` cannot be pushed through any
repetition argument certified by a universal bound
(`black-box-repetition-needs-sqrt-scale-soundness-gap`). A necessary
intermediate rung follows from the squaring law in the equivalence claim:
NP-hardness of `Gap-UG[1 - eta, 1 - L eta]` for arbitrarily large `L`.
