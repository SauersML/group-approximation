---
rg: 2
id: biasymptotic-complement-ideal-ultramatricial-proof
kind: route
title: Corners over clopen V ⊆ X∖Y have uniformly bounded J-chains of visits, so they are unions of algebras of finite principal groupoids
target: biasymptotic-subshift-complement-ideal-is-ultramatricial
requires: []
artifacts:
  - research/artifacts/sk-k2-subsystems-2026-09-13-part1.md
---

The full proof is Proposition C in the artifact.
1. **Localization.** Finitely many r_i ∈ I_Y satisfy e_V r_i e_V = r_i for a clopen V ⊆ X∖Y.
2. **Bounded chains.** The points of V with m visits to V at consecutive gaps ≤ J form a decreasing sequence of clopen sets. If all were nonempty, compactness would give x ∈ V with infinitely many forward visits, so ω(x) ∩ V ≠ ∅, contradicting ω(x) ⊆ Y. So chains have length ≤ M.
3. **The relation.** "Consecutive visits with gaps ≤ J" is a clopen equivalence relation on V, with classes of size ≤ M and time-diameter ≤ MJ.
4. **The subring.** The subring B_{V,J} of Σ f_j u^j supported on related pairs contains e_V, is closed under products by transitivity, and contains every element of e_V R e_V with exponents ≤ J.
5. **Structure.** Class size, position and relative times are locally constant. With them, matrix units ε_pq(W) = e_{T^{s_p}W}u^{s_p−s_q} give B_{V,J} ≅ ∏_k M_k(LC(W_k,F_2)). Finite partitions then give finite subrings ∏ M_k(F_2^c). ∎
