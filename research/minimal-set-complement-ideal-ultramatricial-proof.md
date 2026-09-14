---
rg: 2
id: minimal-set-complement-ideal-ultramatricial-proof
kind: route
title: The complement ideal of a set containing all minimal subsets is ultramatricial, by bounded chains and first-return towers
target: minimal-set-complement-ideal-is-ultramatricial
requires:
  - subshift-visit-chains-are-bounded-off-every-minimal-subset
  - ultramatricial-ideals-have-elementary-congruence-kernels
artifacts:
  - research/artifacts/sk-k2-recurrent-2026-09-13.md
  - research/artifacts/sk-k2-subsystems-2026-09-13-part1.md
---

This is the tower construction of Proposition C in `research/artifacts/sk-k2-subsystems-2026-09-13-part1.md` §4. Its bounded-chain step now comes from `subshift-visit-chains-are-bounded-off-every-minimal-subset` instead of the limit-set hypothesis. Details: `research/artifacts/sk-k2-recurrent-2026-09-13.md` §2.
1. **Localization.** Finitely many r_i ∈ I_Y lie in the corner C_V = e_V R_X e_V, where V = ⋃_j (supp f_j ∪ T^{-j} supp f_j) is clopen and disjoint from Y.
2. **Bounded chains.** Let J bound the exponents. Maximal J-chains of visits to V have at most M elements.
3. **Classes.** x ~ T^t x when the intermediate visits have gaps ≤ J. Classes have at most M points and diameter at most D = (M−1)J, and the relevant sets are clopen.
4. **The subring.** B_{V,J} = {Σ_{|j|≤D} f_j u^j : supp f_j ⊆ {x ∈ V : T^{-j}x ∈ V, T^{-j}x ~ x}} is a subring with unit e_V. It contains every element of C_V with exponents ≤ J.
5. **Structure.** The elements ε_pq(W) = e_{T^{s_p}W}u^{s_p − s_q} are matrix units. So B_{V,J} ≅ ∏_{k_0≤M} M_{k_0}(LC(W_{k_0},F_2)). A finite clopen refinement gives a finite ∏ M_{k_0}(F_2)^{c} containing the r_i.
6. **Consequence.** Lemma B (`ultramatricial-ideals-have-elementary-congruence-kernels`) gives GL_n(R_X,I_Y) = E_n(I_Y), locally finite, for n ≥ 2. □
