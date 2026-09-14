---
rg: 2
id: substitution-subshift-elementary-groups-non-uniform-growth
kind: claim
title: For a primitive aperiodic substitution subshift of constant length 2 (Thue–Morse, period doubling), G_X = EL_3(LC(X,F_2) ⋊ Z) has non-uniform exponential growth
---

**ESTABLISHED (unreviewed; sk-free-8).** Let `X` be the two-sided subshift of a primitive substitution `ζ` of constant length 2 with a non-periodic fixed point. Examples: Thue–Morse `0↦01, 1↦10` and period doubling `0↦01, 1↦00`.
- `R_X = LC(X,F_2) ⋊ Z` satisfies `R_X ≅ M_2(R_X)`.
- So `G_X = EL_3(R_X)`, and every `EL_n(R_X)` with `n ≥ 3`, has **non-uniform exponential growth**.
- Together with `finite-model-subshift-elementary-groups-simple-kazhdan-lef`, `G_X` is an infinite, finitely generated, simple, Kazhdan, LEF (hence sofic) group of non-uniform exponential growth.

**Tower lemma** (artifact part 2, Lemma 5). Let `V ⊆ X` be clopen with `X = V ⊔ TV` and `(V,T²|_V) ≅ (X,T)`.
- Then `ε_00 = e_V`, `ε_11 = e_(TV)`, `ε_10 = ue_V` and `ε_01 = e_V u^(−1)` are matrix units summing to 1.
- The corner `e_V R e_V` is `LC(V,F_2) ⋊_(T²) Z`, which is isomorphic to `R_X`.
- Here `V = ζ(X)`, by `constant-length-substitution-tower-partition`.

Route: `substitution-subshift-elementary-groups-non-uniform-growth-proof`.
