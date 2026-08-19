---
rg: 2
id: hilbert-embeddable-is-representation-realized-proof
kind: route
title: Expand the length in characters and recognize the elementary cone generators
target: hilbert-embeddable-is-representation-realized
requires: []
artifacts:
  - notes/TRUE_HILBERT_EMBEDDABLE_IS_REPRESENTATION_REALIZED.md
---

# Expand in characters and recognize the cone generators

Direct establishment; the complete argument is §1 of the cited note.
`requires: []` is a proof commitment.

**The generators are squared Hilbert-space distances.** For an irreducible
`π_i`, unitary invariance of the Frobenius norm gives
`ψ_i(a⁻¹b) = ½‖π_i(a⁻¹b) − 1‖_F² = ½‖π_i(b) − π_i(a)‖_F²`, a squared distance
in the Hilbert space `(M_{d_i}(ℂ), ‖·‖_F)`. So each `ψ_i` is conditionally
negative definite, and so is every nonnegative combination.

**The cone is everything.** Expand `ℓ = Σ_i b_i χ_i`. The character criterion
(`hilbert-embeddable-length-hyperlinearity`, item 1) gives `b_i ≤ 0` for
nontrivial `i`; and `ℓ(1) = 0` gives `Σ_i b_i d_i = 0`, hence
`b_triv = −Σ_{i≠triv} b_i d_i` and
`ℓ(h) = Σ_{i≠triv}(−b_i)(d_i − χ_i(h))` with `−b_i ≥ 0`. Taking real parts is
harmless since `ℓ` is real and conjugate characters pair up.

**Realization.** Frobenius norms add over direct sums, so integer
multiplicities `a_i` give `ρ = ⊕ π_i^{⊕a_i}` with `½‖ρ(h) − 1‖_F² = ℓ(h)` on
the nose; real multiplicities are handled by rational approximation and
clearing denominators, which costs a positive scalar and an arbitrarily small
uniform error — harmless because the witness constraints are strict
inequalities with room.

**The microstate.** If `ρ` satisfies `‖ρ(x) − 1‖₂ ≤ ε` on the defect set and
`‖ρ(y) − 1‖₂ ≥ c` on the target set, then `ρ ∘ φ` is `(Φ, ε)`-multiplicative
and `(Φ, c)`-separating: `ρ` is a homomorphism, so every multiplicative defect
of `ρ ∘ φ` is `ρ` of a defect of `φ`. The inclusion `sofic ⊆ 𝒞_FU` is the
computation `‖σ − 1‖²_{2,norm} = 2 d_H(σ, 1)` for permutation matrices.
