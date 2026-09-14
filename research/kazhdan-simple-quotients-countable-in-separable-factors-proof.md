---
rg: 2
id: kazhdan-simple-quotients-countable-in-separable-factors-proof
kind: route
title: Ozawa's separability argument, with property (T) on the bimodule L²(M), applied to distinct simple quotients of a Kazhdan group
target: kazhdan-simple-quotients-countable-in-separable-factors
requires: []
artifacts:
  - research/artifacts/sk-strong-7-operator-algebras-2026-09-13.md
---

Credit: the proof of Theorem 2 in N. Ozawa, Proc. Amer. Math. Soc. 132 (2004), 487–490 (arXiv:math/0210411v2). This route re-derives it in the stated generality.

**Setup.**
- `Λ` has property (T). Fix a Kazhdan pair `(E, κ)`: `E ⊂ Λ` finite, `κ > 0`.
- `M` is a II_1 factor with separable predual, in standard form on `L²(M)`, with trace vector `ξ = 1̂` and modular conjugation `J`, so `J x J η = η x*`.
- The `N_i` are pairwise distinct normal subgroups with `Λ/N_i` simple.

**Step 0 (Kazhdan estimate).** Let `π` be a unitary representation, `P` the projection onto its invariant vectors, and `ξ` a unit vector. Then `‖ξ − Pξ‖ ≤ κ⁻¹ max_{s∈E} ‖π(s)ξ − ξ‖`.
- Write `ξ = Pξ + ζ` with `ζ ⊥ ran P`.
- The restriction of `π` to `(ran P)^⊥` has no invariant vectors. So some `s ∈ E` has `‖π(s)ζ − ζ‖ ≥ κ‖ζ‖`.
- Since `π(s)ξ − ξ = π(s)ζ − ζ`, the estimate follows.

**Step 1.**
- Suppose `I_0 = {i : U(M) contains a copy of Λ/N_i}` is uncountable. For `i ∈ I_0`, fix an injective homomorphism `Λ/N_i → U(M)` and let `u_i: Λ → U(M)` be the composite, so `ker u_i = N_i`.
- `Λ/N_i` is simple, hence nontrivial, so some `s` has `u_i(s) ≠ 1`. As the trace is faithful, `‖u_i(s)ξ − ξ‖ = ‖u_i(s) − 1‖_2 > 0`.
- `I_0` is the union over `n` of the sets `{i : sup_s ‖u_i(s)ξ − ξ‖ > 1/n}`, so for some `δ > 0` an uncountable `I_1 ⊆ I_0` has `sup_{s∈Λ} ‖u_i(s)ξ − ξ‖ > δ` for all `i ∈ I_1`.

**Step 2.**
- Choose `ε > 0` with `2ε/κ < δ`.
- The points `(u_i(s)ξ)_{s∈E}`, `i ∈ I_1`, lie in the separable metric space `L²(M)^E`. An uncountable subset of a separable metric space contains two distinct points at distance `< ε`, so there are `i ≠ j` in `I_1` with `max_{s∈E} ‖u_i(s)ξ − u_j(s)ξ‖ < ε`.

**Step 3.**
- Put `π(s) = u_i(s) J u_j(s) J`. Left multiplication by `M` commutes with right multiplication (`JMJ = M'`), so `π` is a unitary representation of `Λ`.
- `π(s)ξ = (u_i(s) u_j(s)*)^`, so `‖π(s)ξ − ξ‖ = ‖u_i(s)u_j(s)* − 1‖_2 = ‖u_i(s) − u_j(s)‖_2 < ε` for `s ∈ E`.
- By Step 0 there is a `π`-invariant `η` with `‖ξ − η‖ < ε/κ`.

**Step 4.**
- Let `Δ = {s ∈ Λ : u_i(s)η = η}`, a subgroup.
  - It contains `N_i`, since `u_i = 1` there.
  - It contains `N_j`: for `s ∈ N_j`, `η = π(s)η = u_i(s) J u_j(s) J η = u_i(s)η`.
  - So `Δ ⊇ N_i N_j`.
- `N_i` and `N_j` are maximal normal subgroups (simple quotients), and they are distinct.
  - `N_iN_j` is normal and contains `N_i`.
  - If `N_iN_j = N_i`, then `N_j ⊆ N_i`, and maximality gives `N_j = N_i`, a contradiction.
  - So `N_iN_j = Λ` and `Δ = Λ`.

**Step 5.** For every `s ∈ Λ`: `‖u_i(s)ξ − ξ‖ ≤ ‖u_i(s)(ξ − η)‖ + ‖η − ξ‖ < 2ε/κ < δ`. This contradicts `i ∈ I_1`, so `I_0` is countable.

**Consequences.** If `L(Λ/N_j)` embeds in `M`, possibly non-unitally, then `U(M)` contains a copy of `Λ/N_j`:
- take `λ_g ↦ ψ(λ_g) + (1 − ψ(1))`;
- this is injective because `ψ(λ_g) = ψ(1)` forces `λ_g = 1`.

So the isomorphism and universality consequences stated in the claim follow. ∎
