---
rg: 2
id: kt-monomial-split-coset-wreaths-collapse-proof
kind: route
title: Intersect the compressor conjugates, push every proper exponent monoid down to N^d by elementary shears, and finish with Suslin
target: kt-monomial-split-coset-wreaths-collapse-to-gamma
requires:
  - theorem-c-separation-iff-infranormal-coset-wreath
  - kt-compressor-stable-overgroups-have-polynomial-content
---

## Step 1: the compressor core is hyperlinear

`Mon` is countable. For `P ∈ Mon`, `Γ ≤ P^(-1)ΔP` because `PΓP^(-1) ≤ Γ`, and
`W_(P^(-1)ΔP) ≅ W_Δ` by Lemma 0 of `theorem-c-separation-iff-infranormal-coset-wreath-proof`.
The Part 1 argument of that proof shows the product of countably many hyperlinear
`X_(Δ_i)` is hyperlinear (closure (C2)). The sets `A_i` have stabilizers `Δ_i`, so
distillation (**D**) makes the wreath over `∩_i Δ_i` hyperlinear. Applied to
`Δ_P = P^(-1)ΔP`, this shows `W_(Δ')` is hyperlinear.

## Step 2: proper monoids lie in a nonnegative half-space

Let `N^d ⊆ M ≠ Z^d` be a submonoid. If `v ∈ M` has all `v_k < 0`, then
`−e_i = v + (−v − e_i)` with `−v − e_i ∈ N^d`, so `−e_i ∈ M` for all `i` and `M = Z^d`.
So `M` misses the open negative orthant `O`. The convex cone `C = R_(≥0)M` also misses
`O`: a point `Σ t_k m_k ∈ O` survives rational perturbation of the `t_k`, and clearing
denominators puts an element of `M` in `O`. Separate the open convex set `O` from `C`.
This gives `λ ≠ 0` with `λ·c ≥ 0` on `C` and `λ·y ≤ 0` on `O`. Since `C ⊇ N^d`,
`λ ≥ 0`.

## Step 3: `∩_(P∈Mon) P^(-1)M = N^d`

`⊇`: `P N^d ⊆ N^d ⊆ M`. `⊆`: let `v` lie in every `P^(-1)M` and suppose `v_i < 0`. If
`λ = λ_i e_i`, take `P = I`: `λ·v = λ_i v_i < 0`, contradiction. Otherwise pick `j ≠ i`
with `λ_j > 0` and `P = I + kE_(ji)`, `k ≥ 0`. Then `Pv ∈ M` and
`λ·Pv = λ·v + kλ_j v_i → −∞`, contradiction.

## Step 4: the core of `Δ_(M,Q)`

`Q` normalizes `E_r(F_q[M])` because it stabilizes `M`, and
`P^(-1)Δ_(M,Q)P = E_r(F_q[P^(-1)M]) ⋊ P^(-1)QP`. Let `(B,u) ∈ Δ' = ∩_P P^(-1)Δ_(M,Q)P`.

*The projection.* `u ∈ Q'' = ∩_P P^(-1)QP`, and each such `u` stabilizes every
`P^(-1)M`. By Step 3 it stabilizes `N^d`, so it permutes the indecomposables `e_i`. So
`Q''` is a finite group of permutation matrices. It equals `π(Δ')`, since `(1,u) ∈ Δ'`,
and `Δ'` is `Mon`-stable (§4 of `kt-compressor-stable-overgroups-polynomial-content-proof`).
So `Q''` is a finite `Mon`-stable subgroup and hence central (§3 there). The only central
permutation matrix is `I`, so `u = 1`.

*The kernel part.* `B ∈ E_r(F_q[P^(-1)M]) ⊆ SL_r(F_q[P^(-1)M])` for all `P`. Matrix
entries lie in `∩_P F_q[P^(-1)M] = F_q[∩_P P^(-1)M] = F_q[N^d] = A`, comparing supports
and using Step 3. So `B ∈ SL_r(A) = EL_r(A) = Γ` (Suslin, `r ≥ 3`). Hence `Δ' = Γ`, and
Step 1 gives part 2.

## Step 5: HNN and half-space candidates

For `t ∈ Mon`, `tΓt^(-1) ≤ Γ`, so `Γ ≤ t^(-1)Γt ≤ t^(-2)Γt^2 ≤ …`. The union is
`E_r(F_q[M_t])` with `M_t = ∪_n t^(-n)N^d`, an increasing union of monoids. It is
normalized by `t` because `tM_t ⊆ M_t` and `t^(-1)M_t ⊆ M_t`. So
`⟨Γ,t⟩ = E_r(F_q[M_t]) ⋊ ⟨t⟩`, and every element of it has the form `(B,t^n)`.

By Perron--Frobenius, `t^T ∈ M_d(N)` has an eigenvector `λ ≥ 0`, `λ ≠ 0`, with
eigenvalue `ρ > 0`, since `t` is invertible. Then
`λ·t^(-n)w = ρ^(-n) λ·w ≥ 0` for `w ∈ N^d`, so `M_t ⊆ {λ·v ≥ 0} ≠ Z^d`. Part 2 applies
with `Q = ⟨t⟩`. The half-space monoid `{λ·v ≥ 0}` with `λ ≥ 0, λ ≠ 0` is a proper
submonoid containing `N^d`, and part 2 applies to any `Q` in its stabilizer.

## Step 6: finite permutation extensions

If `Γ ≤ Δ ≤ Γ ⋊ Perm_d` is `Mon`-stable, then `π(Δ)` is a finite `Mon`-stable group of
permutation matrices, hence central, hence trivial. So `Δ ≤ Γ`. ∎
