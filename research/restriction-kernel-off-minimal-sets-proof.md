---
rg: 2
id: restriction-kernel-off-minimal-sets-proof
kind: route
title: Restriction kernels off the minimal sets, by the splitting of Theorem D and the minimal-set ultramatricial ideal
target: restriction-kernel-relative-elementary-off-minimal-sets
requires:
  - minimal-set-complement-ideal-is-ultramatricial
  - ultramatricial-ideals-have-elementary-congruence-kernels
  - subshift-restriction-kernel-is-relative-elementary
artifacts:
  - research/artifacts/sk-k2-recurrent-2026-09-13.md
---

This is the proof of Theorem D in `research/artifacts/sk-k2-subsystems-2026-09-13-part1.md` §5, with `minimal-set-complement-ideal-is-ultramatricial` applied to Y′ = Y ∪ Z. Details: `research/artifacts/sk-k2-recurrent-2026-09-13.md` §3.
1. **Split.** Y and Z are disjoint closed invariant sets, so R_{Y′} = R_Y × R_Z.
2. **The Y′ kernel.** Y′ contains every minimal subset, so ker π_{Y′} ⊆ GL_n(R_X, I_{Y′}) = E_n(I_{Y′}) ⊆ E_n(I_Y).
3. **Lift the Z part.** A clopen U ⊇ Z with U ∩ Y = ∅ lifts each r ∈ R_Z to an element of e_U R_X ⊆ I_Y restricting to (0,r). So π_{Y′}(E_n(I_Y)) ⊇ 1 × EL_n(R_Z).
4. **Conclude.** For g ∈ ker π_Y choose h ∈ E_n(I_Y) with π_{Y′}(h) = π_{Y′}(g). Then g h^{-1} ∈ ker π_{Y′} ⊆ E_n(I_Y).
5. **K_2.** For n ≥ 3 the K_2 clause is the general identity (EL_n(R) ∩ GL_n(R,I))/E_n(R,I) ≅ coker(K_2(n,R) → K_2(n,R/I)), stated in `subshift-restriction-kernel-is-relative-elementary`. □
