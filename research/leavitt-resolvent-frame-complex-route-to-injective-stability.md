---
rg: 2
id: leavitt-resolvent-frame-complex-route-to-injective-stability
kind: route
title: A relative Khanh frame-complex argument for R_L would give surjective K_2-stability, hence condition (i) of gate 1
target: st-n-leavitt-resolvent-word-problem-reduces-to-k2
requires:
  - leavitt-surjective-k2-stability-implies-injective
  - leavitt-k1-stability-is-one-step
  - leavitt-stabilization-kernels-are-one-step
---

**OPEN route.** It adapts the proof of Khanh's Steinberg comparison criterion (arXiv:2609.08428, Theorem
`thm:raw-criterion`, read in TeX, `gq/src/on/2609.08428/khanh.tex` lines 430--495) to `R_L`. The group is
`E_n(R_L)`, and the target is `St_n(R_L)` modulo the central image `C` of `K_2(n-1)`, rather than `St_n` itself.

**The argument, if its inputs hold.** Fix `n >= 4`.
1. **Frame complex.** Let `X^E_n` be the `E_n(R_L)`-orbit of the standard ordered frames in Khanh's frame complex.
   If `X^E_n` is simply connected, then Brown's theorem presents `E_n(R_L)` from the vertex stabilizer
   `J_E = {j(b, H)}`, the edge stabilizer `K_E`, one edge element `T`, and one triangle relation.
2. **Lifting the stabilizers modulo `C`.**
   - Suppose `H ⊕ 1 in E_n` implies `H in E_(n-1)` (`K_1`-injective stability at `n - 1`), and likewise at `n - 2`.
   - Then Khanh's sections `ℓ, ℓ_0` are well defined into `St_n / C`, where `C` is the image of `K_2(n-1)` on
     coordinates `2, ..., n`. `C` is central by padded centrality, and it equals `j(K_2(n-1))` after a Weyl
     conjugation.
   - The row relation and the Weyl relations lift as in Khanh. In characteristic `0`, use signed transpositions, since
     `w_12^2 = h_12(-1)`, and adjust the presentation.
3. **Surjective stability.** This gives a surjective section `E_n -> St_n / C` of the projection, so `K_2(n) ⊆ C`. That
   is `K_2(n) = j(K_2(n-1))`: surjective `K_2`-stability at `n - 1`.
4. **Condition (i).** `leavitt-surjective-k2-stability-implies-injective` gives `U_(n-1) = 1`. By level independence,
   `U_N = 1` for every `N >= 3`. Then `St_N(R_L)` has solvable word problem.

**Open inputs.**
- **(F) Simple connectivity: now supplied** by `leavitt-resolvent-frame-complex-is-highly-connected`. The full frame complex
  is simply connected for `n >= 4`, and `E_n` is transitive on its frames of size at most `n - 1`, so `X^E_n` may be
  taken to be `X_n` in low dimensions. The former notes follow.
  - Khanh's cone argument needs a simultaneous word multiplier, and the analogue for `R_L` looks available. Take
    isometries `θ_k = s_1^(M_k) s_2` with widely spaced `M_k`. Then `t_2 t_1^(M_i) c s_1^(M_k) s_2 = 0` for `i != k` and
    bounded `c`, because `t_2 s_1 = 0 = t_1 s_2`.
  - Pure infiniteness also looks available: `t_2 t_1^k f s_1^k s_2 = f(k)` for base functions `f`.
  - The cone vectors must be chosen so that the extended frames stay in the `E_n`-orbit.
- **(S1) `K_1`-injective stability at `n - 1` and `n - 2`: now supplied** by `leavitt-ge-rings-have-stable-k1-at-rank-three`,
  via Menal--Moncasi GE (read through Khanh) and the compression `y x z = 1` for `R_L`. So `GL_m(R_L)/E_m(R_L) = Z` for
  `m >= 3`. For `n = 4` the edge stabilizer needs `m = n - 2 = 2`, so take `n >= 5`.
- **Signs (the only remaining input).** The characteristic-`0` Brown presentation: `T^2 = diag(-1, -1, 1, ...)` sends `b_1`
  to `-b_1`, so one more relation is needed, and its lift `w_12^2 = h_12(-1)` must match modulo `C`.

## Progress on the sign step (2026-09-18)

- **An order-`2` edge element in `E_n`.** `[-1] = 0` in `K_1(R_L) = Z`, and `GL_n(R_L)/E_n(R_L) -> K_1` is injective for
  `n >= 3` (`leavitt-ge-rings-have-stable-k1-at-rank-three`). So `diag(-1, 1, ..., 1) in E_n(R_L)`, and hence the honest
  transposition `P_12 = τ̃ · diag(-1, 1, ...)` lies in `E_n(R_L)`, where `τ̃` is the signed transposition. With
  `T = P_12` and `h = P_23`, Brown's presentation is exactly Khanh's, since `T^2 = 1` and `h^2 = 1`.
- **An exact lift.** Refinement of the first coordinate by the Leavitt pair carries `diag(-1, 1, ...)` to
  `diag(-1, -1, 1, ...)`, which is `h_(12)(-1)` in `St_(n+1)`. So `d = D^-1(h_(12)(-1))` lifts `diag(-1, 1, ...)`, and
  conjugation by `d` negates exactly the generators with one index `1`. Then `ω = w_12 d` conjugates every `X_ij(c)` to
  `X_(τ(i)τ(j))(c)` exactly, with `τ = (12)`.
- **What is left.** `ω^2` acts trivially by conjugation, so it is a central element of `K_2(n)`. The argument needs
  `ω^2 in j(K_2(n-1))`, or `ω^2 = 1`, and the braid relation `ω σ(h) ω = σ(h) ω σ(h)` modulo `C`. The rational symbols
  `{-1, -1}` that appear die in `St_n(R_L)` (`algebraic-closure-kills-rational-steinberg-symbols`). The comparison of
  `D^-1(h(-1))` with `h_(12)(-1)` is not yet done.
