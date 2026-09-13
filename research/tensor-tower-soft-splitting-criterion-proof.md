---
rg: 2
id: tensor-tower-soft-splitting-criterion-proof
kind: route
title: Tail halvings are central sequences, and partial traces of central sequences are tail halvings
target: tensor-tower-bundle-trivial-iff-tails-softly-split
requires:
  - closed-extreme-trace-sets-give-r-fibre-w-star-bundles
  - r-fibre-bundle-triviality-iff-uniform-central-halving
artifacts:
  - research/artifacts/tw-projection-starved-bundle-faces-part2-2026-09-12.md
---

Section 2 of the artifact (Proposition T).

1. **Bundle.** `A` is a `C(X̂)`-algebra whose fibres are UHF algebras with unique trace.
   So `T(A) = Prob(X̂)`, and `∂_e T(A) = X̂` is closed. The first prerequisite, with
   `K = X̂`, makes `M` a W*-bundle with fibres `R`.
2. **(⟸).** `p = 1 ⊗ h ∈ A_m`.
   - It commutes exactly with `A_n ⊗ 1`, and `tr(p − p²) ≤ ε` and `|tr p − 1/2| ≤ ε` at
     every point.
   - Letting `n → ∞` and `ε → 0` gives condition (ii) of the second prerequisite.
3. **(⟹).** Take (ii)-sequences `p_j`, approximated by positive contractions in some `A_m`.
   - Fix `n`. On trivializing sets `V_α` of `U_{0,n}` with matrix units `e^α_{ij}`
     (`d = rank U_{0,n}`), and a partition of unity `f_α`, the partial trace
     `Φ = tr_{U_{0,n}} ⊗ id` satisfies `x − 1 ⊗ Φ(x) = Σ_α d^{-1} Σ_{ij} e^α_{ij}[f_α e^α_{ji}, x]`.
   - So `‖p_j − 1 ⊗ Φ(p_j)‖_{2,u} ≤ C_n max ‖[f_α e^α_{ji}, p_j]‖_{2,u} → 0`.
   - `h = Φ(p_j)` is a positive contraction with `tr h = tr p_j` and
     `tr(h − h²) ≤ tr(p_j − p_j²) + 2‖p_j − 1 ⊗ h‖_2`.
4. **General position.** A rank-`R` bundle over a `d`-dimensional base has a trivial
   subbundle of rank `R − ⌈d/2⌉`. When `d ≤ R`, that rank is at least `R/2`.
