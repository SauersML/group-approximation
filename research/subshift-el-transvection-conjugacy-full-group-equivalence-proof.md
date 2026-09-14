---
rg: 2
id: subshift-el-transvection-conjugacy-full-group-equivalence-proof
kind: route
title: Permutation units and Whitehead diagonals conjugate, Kakutani-Rokhlin towers match levels, and periodic finite models with a Livsic loop argument give the transfer function
target: subshift-el-transvection-conjugacy-full-group-equivalence
requires: []
artifacts:
  - research/artifacts/sk-free-3-conjugacy-problem-2026-09-13-part1.md
---

Notation: `R = LC(X,F_2)⋊_T Z` with `(fu^i)(f′u^j) = f(f′∘T^{−i})u^{i+j}`, so `u1_Uu^{−1} = 1_{TU}`; `f = 1_A − 1_B`.

**(3 ⇒ 1).**
- Let `γ = T^k` on the clopen set `U_k`, and put `w = Σ_k 1_{γU_k}u^k`.
- Then `wf′ = (f′∘γ^{−1})w` for every `f′ ∈ LC(X,F_2)`.
- `w′ = Σ_k 1_{U_k}u^{−k}` is a two-sided inverse, since `T^kU_k ∩ T^kU_l = ∅` and `U_k ∩ T^{l−k}U_l = ∅` for `k ≠ l` by injectivity of `γ`.
- So `w1_Aw^{−1} = 1_{γA} = 1_B`.
- In characteristic 2, `e_12(c)e_21(c^{−1})e_12(c)·e_12(1)e_21(1)e_12(1) = diag(c,c^{−1},1)`, and likewise in the indices `2,3`.
- So `k = diag(w,w^{−1},1)·diag(1,w^{−1},w) = diag(w,w^{−2},w) ∈ EL_3(R)`, and `k e_13(r)k^{−1} = e_13(wrw^{−1})`.

**(2 ⇒ 3).**
- Choose a nonempty clopen `Z` on which `g` is constant.
- Split `Z` into the clopen sets `Z_{h,β}`: return time `h`, and itinerary `β` of membership in `A` and `B` for times `j < h`. The levels `T^jZ_{h,β}` partition `X`.
- For `z ∈ Z_{h,β}`, `Σ_{j<h} f(T^jz) = g(T^hz) − g(z) = 0`, so each tower has equally many `A`-levels as `B`-levels.
- A level permutation `σ` sending `A`-levels to `B`-levels, and complements to complements, defines `γ = T^{σ(j)−j}` on `T^jZ_{h,β}`, with `γ ∈ [[T]]` and `γA = B`.

**(1 ⇒ 2).**
- **Bounds.** Let `k e_13(1_A)k^{−1} = e_13(1_B)`. Let `λ` bound the exponents in the entries of `k^{±1}`, `ρ` bound the radii of their coefficients and of `1_A, 1_B`, and let `ℓ ≥ ρ + λ + 1`, `L = 2ℓ + 1`.
- **Model.** For an `N`-periodic `y` whose `L`-windows lie in `L(X)`, `φ(Σ f_ju^j) = Σ D(f_j)P^j` is additive. Here `D(f) = diag(f(window of y at t))` and `P` is the cyclic shift, with `PD(f)P^{−1} = D(f∘T^{−1})` for radius `≤ ℓ−1`. It is multiplicative on all products occurring in `k(I+E_13 1_A) = (I+E_13 1_B)k` and `kk^{−1} = I`.
- **Rank.** `φ(k)` conjugates `I + E_13D(1_A)` to `I + E_13D(1_B)` in `GL_{3N}(F_2)`. So `rank D(1_A) = rank D(1_B)`, i.e. `Σ_{t∈Z/N} f(window of y at t) = 0`.
- **Loops.** Fix `x` with dense forward orbit. If `x[a,a+L) = x[b,b+L)` with `a < b`, then the `(b−a)`-periodic `y` with `y[0,b−a) = x[a,b)` satisfies `y[0,b−a+L) = x[a,b+L)`, so it is admissible. Its loop sum is `S(b+ℓ) − S(a+ℓ)`, where `S(k) = Σ_{i<k} f(T^ix)`. So `S(a+ℓ)` depends only on the `L`-window `x[a,a+L)`.
- **Transfer function.** Setting `g(z) = S(a+ℓ)` for any `a` with `x[a,a+L) = z[−ℓ,ℓ]` defines `g ∈ C(X,Z)`. It satisfies `g(T^{k+1}x) − g(T^kx) = f(T^kx)` for `k ≥ ℓ`, and so `g∘T − g = f` by density.
