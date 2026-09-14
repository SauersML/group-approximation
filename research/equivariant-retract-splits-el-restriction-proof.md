---
rg: 2
id: equivariant-retract-splits-el-restriction-proof
kind: route
title: A continuous equivariant retraction gives a ring section of restriction, which splits EL_n and puts the kernel in E_n(R_X, I_Y)
target: equivariant-retract-splits-subshift-el-restriction
requires: []
artifacts:
  - research/artifacts/sk-k2-recurrent-2026-09-13.md
---

Direct proof; `research/artifacts/sk-k2-recurrent-2026-09-13.md` §6.
1. **Section.** f ↦ f∘r is an equivariant ring homomorphism LC(Y,F_2) → LC(X,F_2), because r∘T = T∘r. With u ↦ u it extends to s : R_Y → R_X. Since r|_Y = id, ρ_Y∘s = id.
2. **Kernel.**
   - Take g ∈ ker π_Y and write g = ∏_t e_{i_tj_t}(r_t). Put r′_t = s(ρ_Y(r_t)) and d_t = r_t − r′_t ∈ I_Y. Then e(r_t) = e(r′_t)e(d_t).
   - Moving each e(d_t) to the right replaces it by a conjugate, so g ∈ (∏_t e(r′_t))·E_n(R_X,I_Y).
   - ∏_t e(r′_t) = EL_n(s)(π_Y(g)) = 1, so g ∈ E_n(R_X,I_Y). The reverse inclusion is clear.
3. **Splitting.** EL_n(s) is a section of π_Y, which gives the semidirect product. For n ≥ 3, St_n(s) is a section of St_n(R_X) → St_n(R_Y) and maps K_2(n,R_Y) into K_2(n,R_X), so the K_2 map is split onto. □
