---
rg: 2
id: separable-ii1-factors-weakly-dense-free-group-cstar-proof
kind: route
title: Norming finite-dimensional representations on vanishing corners give an injective weakly dense image of the full C*(F_infinity)
target: separable-ii1-factors-have-weakly-dense-full-free-group-cstar
requires: []
artifacts:
  - research/artifacts/sk-free-5-brown-q3-2026-09-13-part1.md
---

Complete proof (sk-free-5, 2026-09-13). `M` is a II_1 factor with separable predual and faithful normal tracial state `τ`, `‖x‖_2 = τ(x*x)^{1/2}`. `F_∞` is free on `a_1, a_2, …`.

**Step 1: norming representations.**
- `C*(F_2)` is residually finite-dimensional (M.-D. Choi, Pacific J. Math. 87 (1980), 41–48). `F_∞` is a subgroup of `F_2`, and full group C*-algebras of subgroups embed (induced representations), so `C*(F_∞)` is residually finite-dimensional.
- Pick a dense sequence `(x_l)` in `C*(F_∞)`, and for each `l, n` a finite-dimensional representation `σ` with `‖σ(x_l)‖ > ‖x_l‖ − 1/n`.
- The countable family `(σ_k)` so obtained satisfies `sup_k ‖σ_k(x)‖ = ‖x‖` for all `x`. The left side is a C*-seminorm that agrees with the norm on a dense set, and C*-norms are continuous.
- Enumerate `(ρ_j)_{j≥1}` so that every `σ_k` occurs infinitely often. Let `d_j` be the dimension of `ρ_j`. Then for every `m`,

  `sup_{j≥m} ‖ρ_j(x)‖ = ‖x‖` for all `x ∈ C*(F_∞)`.   (N)

**Step 2: corners.**
- Choose orthogonal projections `q_j ∈ M`, `j ≥ 1`, with `τ(q_j) = 2^{-j-1}`. Put `e_i = 1 − Σ_{j≥i} q_j`, so `τ(1 − e_i) = 2^{-i}` and `e_i ↑ 1`.
- Each `q_jMq_j` is a II_1 factor. Fix a unital *-embedding `θ_j : M_{d_j}(C) → q_jMq_j`, from `d_j` equivalent orthogonal subprojections of `q_j` and partial isometries between them, and put `r_j = θ_j ∘ ρ_j`.

**Step 3: target unitaries.** `M` has separable predual, so it is generated as a von Neumann algebra by a sequence of unitaries `(y_k)`. Every element is a combination of four unitaries. Fix `κ : N → N` with every fibre infinite.

**Lemma U.** If `y ∈ U(M)`, `e ∈ M` is a projection and `δ = τ(1 − e)`, there is `w ∈ U(eMe)` with `‖w − eye‖_2 ≤ δ^{1/2}`.
- Put `x = eye`. Then `x*x = e − ey*(1−e)ye`, so `‖e − x*x‖_2 ≤ ‖(1−e)ye‖_2 ≤ ‖1−e‖_2 = δ^{1/2}`.
- Write `x = v|x|` (polar decomposition in the finite algebra `eMe`) and extend `v` to a unitary `w ∈ eMe` with `x = w|x|`. The projections `e − v*v` and `e − vv*` are equivalent in a finite von Neumann algebra.
- Then `‖w − x‖_2 = ‖e − |x|‖_2 ≤ ‖e − |x|²‖_2 ≤ δ^{1/2}`, using `1 − t ≤ 1 − t²` on `[0,1]`.

**Step 4: generators.**
- For `i ≥ 1` take `w_i ∈ U(e_iMe_i)` from Lemma U with `y = y_{κ(i)}` and `e = e_i`, and set

  `z_i = w_i + Σ_{j≥i} r_j(a_i)`.

- The projections `e_i` and `q_j` (`j ≥ i`) are orthogonal with sum `1`, so `z_i ∈ U(M)`. The sum converges strongly.
- Let `π : C*(F_∞) → M` be the unital *-homomorphism with `π(a_i) = z_i` (universal property).

**Step 5: injective.**
- Let `x` be a noncommutative polynomial in `a_1^{±1}, …, a_m^{±1}`. For `j ≥ m` and `i ≤ m`, `q_j ≤ 1 − e_i`, so `z_i^{±1}q_j = q_jz_i^{±1} = r_j(a_i^{±1})`. So `q_j` commutes with `π(x)` and `π(x)q_j = θ_j(ρ_j(x))`.
- `θ_j` is isometric, so `‖π(x)‖ ≥ ‖ρ_j(x)‖` for all `j ≥ m`. By (N), `‖π(x)‖ ≥ ‖x‖`, and `‖π(x)‖ ≤ ‖x‖` holds for every *-homomorphism.
- So `π` is isometric on the dense *-subalgebra `C[F_∞]`, hence on `C*(F_∞)`.

**Step 6: weakly dense.** Fix `k` and `i ∈ κ^{-1}(k)`, and let `δ_i = 2^{-i}`. Decompose along `e_i` and `1 − e_i`:
- `‖z_i − y_k‖_2 ≤ ‖w_i − e_iy_ke_i‖_2 + ‖e_iy_k(1−e_i)‖_2 + ‖(1−e_i)y_ke_i‖_2 + ‖Σ_{j≥i} r_j(a_i) − (1−e_i)y_k(1−e_i)‖_2`.
- The first term is at most `δ_i^{1/2}` by Lemma U. The next two are at most `‖1−e_i‖_2 = δ_i^{1/2}`. The last is an operator of norm `≤ 2` supported under `1 − e_i`, so it is at most `2δ_i^{1/2}`.
- So `‖z_i − y_k‖_2 ≤ 5·2^{-i/2} → 0` along the infinite set `κ^{-1}(k)`.
- In the standard representation on `L²(M)`, `‖(z_i − y_k)x̂‖ = ‖(z_i − y_k)x‖_2 ≤ ‖z_i − y_k‖_2 ‖x‖`. So `z_i → y_k` strongly on the dense set `M̂`, and, being uniformly bounded, strongly on `L²(M)`.
- So `y_k ∈ π(C*(F_∞))''` for every `k`, and `π(C*(F_∞))'' = M`.

**Step 7: properties of the image.** `A = π(C*(F_∞)) ≅ C*(F_∞)` is separable and residually finite-dimensional. Separable residually finite-dimensional C*-algebras are quasidiagonal. `C*(F_∞)` has the local lifting property (Kirchberg, Invent. Math. 112 (1993)). ∎

**Model test.**
- For `M = R`, the statement is consistent with `R` containing the AF algebras, which are also QD.
- The construction never uses property (T), Connes-embeddability or fullness, so it applies to every separable II_1 factor.
- `π` is not trace-preserving for a trace on `C*(F_∞)` fixed in advance. The trace `τ∘π` is determined by the construction, and its GNS factor is `M`.
