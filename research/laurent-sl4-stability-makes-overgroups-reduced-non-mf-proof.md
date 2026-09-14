---
rg: 2
id: laurent-sl4-stability-makes-overgroups-reduced-non-mf-proof
kind: route
title: Restrict the MF embedding to the Laurent lattice, lift, correct by stability, and meet the congruence invariant vector
target: laurent-sl4-stability-makes-overgroups-reduced-non-mf
requires:
  - laurent-sl-n-representations-have-sl2-invariant-vectors
  - ring-model-permutation-vectors-block-strong-convergence
artifacts:
  - research/artifacts/sk-matricial-stability-laurent-sl4-2026-09-13.md
---

Let `Q = ∏_n M_{k_n}(C) / ⊕_n M_{k_n}(C)` and suppose `ι : C*_r(Γ) → Q` is an injective *-homomorphism, with
`Λ = SL_4(F_q[t,t^{-1}]) ≤ Γ`.

0. **Restriction.** `λ_Γ|_Λ` is a multiple of `λ_Λ`, so `C*_r(Λ) → C*_r(Γ)` is isometric, and `ι` restricts to an
   injective *-homomorphism of `C*_r(Λ)`. It is isometric.
1. **Lift.** For `g ∈ Λ`, `ι(λ(g))` is a unitary of `Q`. Lift it to `(x_n) ∈ ∏ M_{k_n}` and let `φ_n(g)` be a unitary
   from a polar decomposition of `x_n`. Since `x_n^*x_n → 1` and `x_nx_n^* → 1` in norm, `(φ_n(g))` still represents
   `ι(λ(g))`. As `g ↦ ι(λ(g))` is a homomorphism, `‖φ_n(gh) − φ_n(g)φ_n(h)‖ → 0` for all `g, h`.
2. **Correct.** Stability of `Λ` gives homomorphisms `π_n : Λ → U(k_n)` with `‖π_n(g) − φ_n(g)‖ → 0`. So
   `(π_n(x)) ↦ ι(λ(x))` in `Q` for every `x ∈ C[Λ]`. The norm of `Q` is `limsup_n` of the coordinate norms and `ι` is
   isometric, so `limsup_n ‖π_n(x)‖ = ‖λ_Λ(x)‖`.
3. **Witness.**
   - By item 3 of `ring-model-permutation-vectors-block-strong-convergence` (Nagao), `SL_2(F_q[t])` contains free
     generators `S, T` of a free group of rank 2. Place them in the upper-left block of `Λ` and put
     `z = S + S^{-1} + T + T^{-1}`.
   - `λ_Λ` restricted to `⟨S,T⟩` is a multiple of `λ_{F_2}`, so `‖λ_Λ(z)‖ = 2√3` (Kesten).
   - Each `π_n` with `k_n ≥ 1` is a finite-dimensional unitary representation of `Λ`. By
     `laurent-sl-n-representations-have-sl2-invariant-vectors` it has a unit vector fixed by the upper-left
     `SL_2(F_q[t,t^{-1}])`, which contains `S` and `T`. So `‖π_n(z)‖ = 4`.
   - `ι` is injective on the infinite-dimensional algebra `C*_r(Λ)`, so `k_n ≥ 1` for infinitely many `n`, and the
     `limsup` in step 2 runs over those `n`. Then `4 ≤ ‖λ_Λ(z)‖ = 2√3`, a contradiction.

Step 3 needs the eigenvalue `4` in every coordinate. That is why genuine same-dimension correction is required: the
padded (weak) form of stability does not suffice, since padding may carry the eigenvalue.
