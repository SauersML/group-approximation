---
rg: 2
id: leavitt-triangular-endomorphism-commutants-are-finite-proof
kind: route
title: Last-letter supports bound the level, a Schmidt-rank cut bounds the degree, and top components reduce triangular units to the core
target: leavitt-triangular-endomorphism-commutants-are-finite
requires: []
artifacts:
  - research/artifacts/leavitt-relative-commutants-2026-09-13.md
---

The full proofs are in `research/artifacts/leavitt-relative-commutants-2026-09-13.md` (Theorems 1 and 2,
Corollary 3). Write `R_d^(n) = Hom(V^⊗n, V^⊗(n+d))` with `V = K^2`. Lifting a level appends `1_V`, and
`phi` prepends `1_V`.

1. **Grading.** For core `u`, `u s_i` is homogeneous. So the components of `z ∈ C_u` lie in `C_u`.
2. **Level.** At level `n >= k` with `n + d >= k`, the equation
   `Z ⊗ 1_V = (U ⊗ 1)(1_V ⊗ Z)(U^(-1) ⊗ 1)` has `U` acting on neither last letter. The left side splits off
   the last letter, so `Z` does too, and the level drops. The descent stops when `min(n, n + d) <= k - 1`.
3. **Degree.** For `d >= 1`, iterate to `Z ⊗ 1_n = (U_n ⊗ 1_d)(1_n ⊗ Z) U_n^(-1)` with
   `u_n = u phi(u) ... phi^(n-1)(u)` and `n >= d`. Across the cut {inputs, first `N` outputs} | {last `d` outputs},
   invertible conjugation preserves Schmidt rank. The left side has rank `2^d` (identity wires). The right
   side has rank at most `4^(k-1)`, the `A`-part of `Z`. So `d <= 2k - 2`. The anti-automorphism `τ`,
   `s_α t_β -> s_β t_α`, maps `C_u` onto `C_(τ(u)^(-1))` and reverses degrees.
4. **Triangular units.** For `u ∈ H_<=`, the top component `z_D` of `z ∈ C_u` satisfies
   `z_D u_0 s_i = u_0 s_i z_D`, so it lies in `C_(u_0)`. Filtering by top degree gives
   `dim C_u <= dim C_(u_0)`. For `H_>=`, apply `τ`.
5. **Question 5.7.** `f(1 ⊗ -)` maps `L` unitally into `C_u`. Its image `B` satisfies `B ≅ B ⊕ B` as a left
   module, so `B` is infinite-dimensional. Twisting by `w` gives the unit `w u phi(w)^(-1)`, since
   `s_i w^(-1) = phi(w^(-1)) s_i`. Flipping the factors handles `v`. ∎
