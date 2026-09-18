---
rg: 2
id: artin-f-n-iff-maximal-free-of-infinity-parabolics-f-n-proof
kind: route
title: "Proof: combine the free-of-infinity reduction with descent of F_n to standard parabolic subgroups"
target: artin-f-n-iff-maximal-free-of-infinity-parabolics-f-n
requires:
  - artin-type-f-n-reduces-to-free-of-infinity-graphs
  - artin-type-f-n-passes-to-standard-parabolic-subgroups
---

Standard parabolic subgroups are identified with the Artin groups of induced subgraphs
(van der Lek; also recovered in `artin-type-f-n-passes-to-standard-parabolic-subgroups-proof`,
Section 3), and a parabolic subgroup of a parabolic subgroup is the parabolic subgroup of `Γ`
on the same subset.

(⇒) Each `X_i ⊆ S`; apply `artin-type-f-n-passes-to-standard-parabolic-subgroups`.

(⇐) Let `Y ⊆ S` be free of infinity. Since `S` is finite, `Y ⊆ X_i` for some `i`. By
`artin-type-f-n-passes-to-standard-parabolic-subgroups` applied to `Γ_{X_i}` and `Y ⊆ X_i`,
`A_Y` is of type `F_n`. This holds for every free-of-infinity `Y`, so `A_Γ` is of type `F_n`
by `artin-type-f-n-reduces-to-free-of-infinity-graphs`.

(Formula.) Apply the equivalence for each finite `n`: `A_Γ` is `F_n` iff `n ≤ fl(A_{X_i})`
for all `i`. The inequality `fl(A_{Γ_T}) ≥ fl(A_Γ)` is the descent claim for each `n`.

(Minimal counterexample.) Among induced subgraphs `Γ_T` with `A_T` not of type `F_∞`
(nonempty if `A_Γ` fails), choose `T` minimal. Every proper `T' ⊊ T` gives type `F_∞`. If `T`
were not free of infinity, every maximal free-of-infinity subset of `T` would be proper, hence
`F_∞`, and (⇐) would make `A_T` of type `F_∞`. Upward closure is the contrapositive of (⇒)
for the pair `T ⊆ S'`. ∎
