---
rg: 2
id: subshift-elementary-groups-contain-laurent-sl-n-lattices-proof
kind: route
title: Corners over towers and first-return units put SL_3k over Laurent polynomials inside EL_3 of the subshift algebra
target: subshift-elementary-groups-contain-laurent-sl-n-lattices
requires:
  - tower-subshift-elementary-group-is-el-3k-of-base
---

Write `e_U` for the indicator of a clopen set `U`, so `u e_U u^{-1} = e_{TU}`. Every element of `R` is uniquely
`Σ_j f_j u^j`.

1. **Tower corner.** `T` has no periodic points, since `X` is infinite and minimal. So some nonempty clopen `V` has
   `V, TV, …, T^{k-1}V` pairwise disjoint. Put `W = V ⊔ … ⊔ T^{k-1}V` and `ε_ij = u^i e_V u^{-j}` for
   `0 ≤ i,j < k`.
   - `ε_ij ε_i'j' = u^i e_V e_{T^{i'-j}V} u^{i'-j-j'}`. This equals `ε_ij'` if `i' = j`, and `0` otherwise, because
     `V ∩ T^{i'-j}V = ∅` for `0 < |i'-j| < k`.
   - `Σ_i ε_ii = e_W`.
   - So `e_W R e_W ≅ M_k(S)` with `S = e_V R e_V`, through `x ↦ (ε_{0i} x ε_{j0})_{ij}`.
2. **First-return unit.** By minimality every point of `V` returns to `V`. By compactness the first-return time
   takes finitely many values `r ≥ 1`, on clopen sets `V_r` partitioning `V`. Put `u_V = Σ_r u^r e_{V_r}`.
   - `u_V ∈ S`, and `u_V^{-1} = Σ_r e_{V_r} u^{-r} ∈ S`.
   - For `a ∈ Z`, `u_V^a = Σ_j e_{T^j V_{a,j}} u^j`, where `V_{a,j} = {x ∈ V : r_a(x) = j}` and `r_a(x)` is the
     `a`-th return time of `x` (negative for `a < 0`).
   - For fixed `x` the map `a ↦ r_a(x)` is injective. Given a nonzero finite sum `Σ_a c_a u_V^a` and `x ∈ V`, pick
     `a_0` with `c_{a_0} ≠ 0` and put `j = r_{a_0}(x)`. The coefficient of `u^j` at `T^j x` is `c_{a_0} ≠ 0`.
   - So `t ↦ u_V` is an injective ring homomorphism `F_q[t,t^{-1}] → S`.
3. **Corner embedding.** For `x, y ∈ M_3(e_W R e_W)` we have `x(1-e_W) = 0 = (1-e_W)y`. So
   `x ↦ x + (1-e_W)I_3` is an injective homomorphism `GL_3(e_W R e_W) → GL_3(R)`. It sends `e_ij(s)` to
   `e_ij(s)`, so it maps `EL_3(e_W R e_W)` into `G_X`.
4. **Assembly.**
   - `EL_3(M_k(S)) = EL_{3k}(S)` by item 3 of `tower-subshift-elementary-group-is-el-3k-of-base`.
   - `EL_{3k}(F_q[t^{±1}]) ≤ EL_{3k}(S)` through step 2.
   - `F_q[t^{±1}]` is a Euclidean domain, so row reduction gives `EL_{3k}(F_q[t^{±1}]) = SL_{3k}(F_q[t^{±1}])`.
   - Composing with steps 1 and 3 embeds `SL_{3k}(F_q[t^{±1}])` in `G_X`. `SL_n` is an upper-left block of
     `SL_{3k}` for `n ≤ 3k`.
5. **Reduced algebras.** For `H ≤ Γ`, `λ_Γ|_H` is a multiple of `λ_H`, so `C*_r(H) → C*_r(Γ)` is isometric. An
   MF embedding of `C*_r(Γ)` restricts to one of `C*_r(H)`.
