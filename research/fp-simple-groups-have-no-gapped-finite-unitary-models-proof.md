---
rg: 2
id: fp-simple-groups-have-no-gapped-finite-unitary-models-proof
kind: route
title: Separation bounds the trivial isotypic weight, the gap makes relator images central, and a finite projective image of a simple group collapses the commutators
target: fp-simple-groups-have-no-gapped-finite-unitary-models
requires: []
---

**Setup.** Let `S = ⟨X | R⟩` with `X` and `R` finite. Suppose `φ_k`, `ρ_k` and `π_k = ρ_k∘φ_k` induce an injective homomorphism
`Π : S → ∏_ω (U(d_k), ‖·‖_2)`.
- `τ` is the normalized trace. For a unitary `U`, `‖U − I‖_2² = 2 − 2 Re τ(U)`.
- `S` is infinite and simple, so it is nonabelian. Fix `x, y ∈ X` with `c = [x,y] = xyx^{-1}y^{-1} ≠ e` in `S`.

**Step 0 (words).** Let `w = x_1^{ε_1}⋯x_m^{ε_m}` be a word in `X`, with image `w̄ ∈ S`. Put
`W_k(w) = φ_k(x_1)^{ε_1}⋯φ_k(x_m)^{ε_m} ∈ Q_k`. Then `lim_ω ‖ρ_k(W_k(w)) − π_k(w̄)‖_2 = 0`.
- `Π` is a homomorphism, so `lim_ω ‖π_k(g)π_k(h) − π_k(gh)‖_2 = 0` and `lim_ω ‖π_k(g^{-1}) − π_k(g)^{-1}‖_2 = 0`.
- On unitaries, `‖AB − A'B'‖_2 ≤ ‖A − A'‖_2 + ‖B − B'‖_2`.
- `ρ_k` is a homomorphism, so `ρ_k(W_k(w)) = π_k(x_1)^{ε_1}⋯π_k(x_m)^{ε_m}`.

Injectivity: for `g ≠ e`, `η_g := lim_ω ‖π_k(g) − I‖_2 > 0`, because `lim_ω ‖π_k(e) − I‖_2 = 0` and `Π(g) ≠ 1`.

**Step 1 (trivial isotypic weight).** Let `w_k^0` be the normalized dimension of the trivial isotypic component of `ρ_k`.
- Every `ρ_k(q)` fixes that component pointwise, so `‖ρ_k(q) − I‖_2² ≤ 4(1 − w_k^0)` for all `q ∈ Q_k`.
- Take `q = φ_k(c)`. Then `lim_ω (1 − w_k^0) ≥ η_c²/4 > 0`.

**Step 2 (the gap).** Decompose `ρ_k` into irreducible constituents `χ` with multiplicities `m_χ`. For noncentral `q`:
```
Re τ(ρ_k(q)) = w_k^0 + Σ_{χ≠1} (m_χ χ(1)/d_k) Re(χ(q)/χ(1)) ≤ w_k^0 + (1 − w_k^0) θ,
```
so `‖ρ_k(q) − I‖_2² ≥ 2(1 − θ)(1 − w_k^0)`. By Step 1, for ω-almost all `k`, every noncentral `q ∈ Q_k` has
`‖ρ_k(q) − I‖_2² ≥ δ := (1 − θ) η_c²/4 > 0`.

**Step 3 (relators are central).** For `r ∈ R`, `r̄ = e`. So by Step 0, `lim_ω ‖ρ_k(W_k(r)) − I‖_2 = 0`. There are finitely many
relators, so by Step 2, for ω-almost all `k`, `W_k(r) ∈ Z(Q_k)` for every `r ∈ R`.

**Step 4 (projective image).** For such `k`, `x ↦ φ_k(x) Z(Q_k)` defines a homomorphism `F(X) → Q_k/Z(Q_k)` that kills `R`.
- So it factors through a homomorphism `ψ_k : S → Q_k/Z(Q_k)`.
- Its kernel is normal in the simple group `S`, and it is nontrivial because `S` is infinite and `Q_k` is finite. So
  `ker ψ_k = S`, and `φ_k(x) ∈ Z(Q_k)` for every `x ∈ X`.

**Step 5 (contradiction).** Central elements commute, so `W_k(xyx^{-1}y^{-1}) = 1` for ω-almost all `k`. By Step 0,
`η_c = lim_ω ‖π_k(c) − I‖_2 = lim_ω ‖ρ_k(1) − I‖_2 = 0`, which contradicts Step 1. ∎

**Remarks.**
- Only the gap at the constituents that occur in `ρ_k` is used. So "θ-gapped" can be weakened to a gap at those constituents.
- Finite presentation is used exactly once, in Step 4, to turn "finitely many relators central" into a homomorphism.
  Simplicity and infiniteness are used exactly once, to make that homomorphism trivial.
- No property (T) is used.
- This is the unitary, character-ratio analog of the minimum-distance observation behind
  `gap-sofic-approximations-are-local-embeddings`. It is folklore-level. The new point is the one-sided form: the gap is needed
  only at noncentral elements, and the conclusion needs no local embedding step.
