---
rg: 2
id: kazhdan-group-factor-popa-corners-vanishing-trace-proof
kind: route
title: Spectral gap of the conjugation representation against a half-trace projection in the relative commutant of the Popa corner
target: kazhdan-group-factor-popa-corners-have-vanishing-trace
requires: []
artifacts:
  - research/artifacts/sk-free-5-brown-q3-2026-09-13-part1.md
---

Complete proof (sk-free-5, 2026-09-13). The notation is that of the target claim.

**Step 1: spectral gap.**
- `G` acts on `L²(M) = ℓ²(G)` by conjugation, `ξ ↦ λ_gξλ_g*`. This is a unitary representation, and `C1 = Cδ_e` is invariant.
- On `ℓ²(G∖{e})` an invariant vector is constant on conjugacy classes and square-summable. Every nontrivial class is infinite (ICC), so there is no nonzero invariant vector.
- By the definition of a Kazhdan pair, `max_{s∈S}‖λ_sξλ_s* − ξ‖_2 ≥ ε_S‖ξ‖_2` for every `ξ ∈ ℓ²(G∖{e})`.
- For `x ∈ M` take `ξ = x − τ(x)1`. Then `‖λ_sξλ_s* − ξ‖_2 = ‖[λ_s, x]‖_2`, so

  `‖x − τ(x)‖_2 ≤ ε_S^{-1} max_{s∈S} ‖[λ_s, x]‖_2`.   (SG)

**Step 2: a half-trace projection commuting with `B`.**
- Write `B = ⊕_r M_{n_r}(C)` with matrix units `f^{(r)}_{ab}`, so `p = Σ_r Σ_a f^{(r)}_{aa}`.
- `M` is a II_1 factor (`G` ICC), so each corner `f^{(r)}_{11}Mf^{(r)}_{11}` is a II_1 factor. Choose a projection `g_r ≤ f^{(r)}_{11}` with `τ(g_r) = τ(f^{(r)}_{11})/2`.
- Put `e = Σ_r Σ_a f^{(r)}_{a1} g_r f^{(r)}_{1a}`.
- Then `e` is a projection, `e ≤ p`, `e` commutes with every `f^{(r)}_{ab}` (hence with `B`), and `τ(e) = Σ_r n_r τ(f^{(r)}_{11})/2 = τ(p)/2`.

**Step 3: `e` almost commutes with `y_s` in norm.** Decompose `y = y_s` along `p` and `1 − p`:
- `[e, (1−p)y(1−p)] = 0`, since `e(1−p) = (1−p)e = 0`.
- `[e, py(1−p)] = ey(1−p)` has norm at most `‖py(1−p)‖ = ‖[p, y](1−p)‖ ≤ η`. Likewise `‖[e, (1−p)yp]‖ ≤ η`.
- Choose `b ∈ B` with `‖pyp − b‖ ≤ η`. Since `[e, b] = 0`, `‖[e, pyp]‖ ≤ 2η`.
- So `‖[e, y_s]‖ ≤ 4η`, and therefore `‖[e, y_s]‖_2 ≤ 4η`.

**Step 4: conclusion.**
- `‖[e, λ_s]‖_2 ≤ ‖[e, y_s]‖_2 + ‖[e, λ_s − y_s]‖_2 ≤ 4η + 2‖λ_s − y_s‖_2 ≤ 4η + 2δ`, using `‖ex‖_2, ‖xe‖_2 ≤ ‖x‖_2`.
- By (SG), `‖e − τ(e)‖_2 ≤ ε_S^{-1}(4η + 2δ)`.
- `‖e − τ(e)‖_2² = τ(e)(1 − τ(e)) ≥ τ(e)/2 = τ(p)/4`, because `τ(e) ≤ 1/2`.
- So `τ(p) ≤ 4ε_S^{-2}(4η + 2δ)²`. ∎

**Model tests.**
- `G = Z` is amenable, not Kazhdan, and `R = L(Z)`-type algebras have Popa corners of trace near 1. Step 1 fails there, as it should.
- In `separable-ii1-factors-have-weakly-dense-full-free-group-cstar`, the corners `q_j` (`j ≥ m ≥ i`) serve `z_1, …, z_m` with `η = 0` and `δ ≈ 5·2^{-i/2}`. The bound allows trace up to `400ε_S^{-2}2^{-i}`, and indeed `τ(q_j) ≤ 2^{-i-1}`.
