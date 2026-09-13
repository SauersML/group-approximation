---
rg: 2
id: bauer-divisible-unit-rank-density-proof
kind: route
title: Divide the unit, cut it with central step functions of the extreme boundary, and pull the result back into A
target: bauer-tracially-divisible-unit-gives-bounded-rank-density
requires: []
artifacts:
  - research/artifacts/ex-toms-winter-bauer-divisible-unit-2026-09-12.md
---

**Direct proof.** Section 1 of the artifact. `K = ∂_e T(A)`, `λ ∈ K` extreme
traces, `‖x‖_{2,u} = sup_λ λ(x*x)^{1/2}`.

1. **One matrix size.** Split `f: T(A) → [0,k]` as `Σ_r min(max(f|_K − (r−1),0),1)`,
   each extended affinely (Bauer), and take a direct sum. So `f ∈ C(K,[0,1])`.
2. **Divided unit.** Take `N ≥ 8/η` and order zero `φ: M_N → A` with
   `τ(1 − φ(1)) < η/8`. By the Winter–Zacharias structure theorem the
   `e_j = φ(e_jj)` are orthogonal. Also `τ(e_j) = τ(h)/N` and
   `τ(e_j − e_j²) = τ(h − h²)/N`, where `h = φ(1)`, through the partial isometries
   `φ^{1/2}(e_1j)` and `φ(e_1j)`.
3. **Central step functions.**
   - Ozawa, arXiv:1304.3523, Theorem 3, read on MSI: there is a unital
     `*`-homomorphism `θ: B(∂S) → Z(N)` with `τ(θ(f)a) = ∫ f(λ)λ(a)dμ_τ`, and
     `A^st ∩ Z(N) = θ(Z(Aff(S)))`, which is `θ(C(K))` for Bauer `S`.
   - Choose a partition of unity `φ_i` on which `f` varies by less than `η/4`, and put
     `r_i = ⌊N f(λ_i)⌋`, `ψ_j = Σ_{r_i ≥ j} φ_i` and `B = Σ_j θ(ψ_j) e_j`.
4. **Estimates at `λ ∈ K`.** Only fewer than `Nη/2 + 1` indices have
   `0 < ψ_j(λ) < 1`. Hence:
   - `λ(B − B²) = Σ_j (ψ_j − ψ_j²)(λ)λ(e_j) + Σ_j ψ_j(λ)²λ(e_j − e_j²) < η/3`;
   - `λ(B) = λ(h)Σ_i φ_i(λ)r_i/N`, which is within `η/2` of `f(λ)`.
5. **Into `A`.**
   - By `A^u = A^st` (Ozawa, lines 123–139), each `θ(ψ_j)` is a 2-norm limit of a
     norm-bounded sequence in `A`. Real parts and polynomial clipping give positive
     contractions `c_j ∈ A` with `‖c_j − θ(ψ_j)‖_{2,u} < η/(12N)`.
   - Put `b = Σ_j e_j^{1/2}c_je_j^{1/2}`. Then `0 ≤ b ≤ 1` and `‖b − B‖_{2,λ} < η/12`,
     so `λ(b − b²) < 7η/12` and `|λ(b) − f(λ)| < 7η/12`.
6. **All traces.** Integrate against the representing measures: `τ(b) = ∫ λ(b)dμ_τ`
   and `f(τ) = ∫ f dμ_τ`. ∎
