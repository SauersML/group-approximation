---
rg: 2
id: self-similar-interval-numerations-force-perron-slopes-proof
kind: route
title: The lengths of a sink component are a positive fixed vector of M(λ) = Σ C_k λ^k; det(I − M(x)) has constant term 1, and Perron–Frobenius monotonicity bounds every conjugate
target: self-similar-interval-numerations-force-perron-slopes
---

**Setup.**
- Let the λ-numeration have types `𝒮`. For each `k ≥ 1` let `C_k` be the nonnegative integer matrix whose `(s,t)` entry
  counts the pieces of type `t` and exponent `k` in the cut of type `s`.
- Put `M(x) = Σ_k C_k x^k`, a finite sum. Every entry is a polynomial with nonnegative integer coefficients and zero
  constant term.
- Additivity of length gives `M(λ)L = L`, where `L = (L_s) > 0`.

**Step 1 (a sink component).**
- In the type graph (`s → t` when a piece of type `t` occurs in the cut of `s`) every vertex has an out-edge. So there
  is a strongly connected component `S` with no edges leaving it, and it contains a cycle.
- The equations for `s ∈ S` involve only types in `S`, so `M_S(λ)L_S = L_S`, with `M_S` the `S × S` block. `M_S(t)` is
  irreducible for every `t > 0`.

**Step 2 (β is an algebraic integer).**
- `P(x) := det(I − M_S(x))` lies in `Z[x]`, and `P(0) = det I = 1`. Since 1 is an eigenvalue of `M_S(λ)`, `P(λ) = 0`.
- So `λ` is algebraic; in particular a transcendental `λ` admits no numeration.
- With `D = deg P`, the polynomial `x^D P(1/x)` has leading coefficient `P(0) = 1` and root `β = 1/λ`. So `β` is an
  algebraic integer.

**Step 3 (no conjugate of β is larger).**
- **Spectral radius at λ.** `M_S(λ)` is nonnegative and irreducible, with a positive eigenvector `L_S` for the
  eigenvalue 1. By Perron–Frobenius, `ρ(M_S(λ)) = 1`.
- **At a conjugate.** Let `σ` be a field embedding of `Q(λ, (L_s)_{s∈S})` into `C`. One exists extending any embedding
  of `Q(λ)`, since `C` is algebraically closed of infinite transcendence degree. Put `z = σ(λ)`. Then
  `M_S(z)σ(L_S) = σ(L_S)`, and `σ(L_S) ≠ 0`. So `ρ(M_S(z)) ≥ 1`.
- **Comparison.** Entrywise `|M_S(z)| ≤ M_S(|z|)`, because the coefficients are nonnegative. So
  `ρ(M_S(z)) ≤ ρ(M_S(|z|))`, since `ρ(A) ≤ ρ(B)` whenever `|A| ≤ B` entrywise.
- **If `|z| < λ`.** Then `0 ≤ M_S(|z|) ≤ M_S(λ)`, and the inequality is strict in every nonzero entry (zero constant
  terms). For irreducible nonnegative matrices, a strictly smaller comparable matrix has strictly smaller spectral radius.
  So `ρ(M_S(|z|)) < 1`, a contradiction.
- **Hence** `|σ(λ)| ≥ λ` for every conjugate, that is, `|σ(β)| ≤ β`. ∎

**Item 1 directly (the 2-adic form, for λ = 2/3).** Let `v` be the 2-adic valuation. Every piece has
`v(λ^k L_t) = k + v(L_t) > v(L_t)`. Take `s` with `v(L_s)` minimal. Then `L_s` is a sum of pieces, each of valuation
`> v(L_s)`, so by the ultrametric inequality `v(L_s) > v(L_s)`. That is a contradiction. The same argument works for
any finite place `w` with `|λ|_w < 1`, which gives Step 2 again.

**The V_{2/3} facts in the target.**
- Tanner's Lemma (Li, Prop. 5.5) gives `H_0 = Γ/(1−λ)Γ` and `H_k = H_{k+1}(Γ ⋊ Λ)` for `k ≥ 1`.
- For `Γ = Z[1/6]` and `λ = 2/3`: `1 − λ = 1/3` is a unit of `Z[1/6]`, so `H_0 = 0`.
- By the Wang sequence, `H_2(Γ ⋊ Z)` is an extension of `H_1(Z; H_1(Γ))` by `H_0(Z; H_2(Γ))`. Here `H_2(Γ) = Λ²Γ = 0`, since `Γ` is torsion-free of rank 1, and
  `H_1(Z; Γ) = ker(λ − 1) = 0`. So `H_1 = 0`.
- The AH sequence gives `V^ab = 0`.
- Simplicity, 2-generation and the Stein embedding are as cited in the target.
