---
rg: 2
id: clifford-diagonal-lamp-subspace-proof
kind: route
title: A trivial diagonal lamp subspace would embed W in a permutation ultraproduct
target: clifford-diagonal-lamp-subspace
requires: [wreath-not-sofic]
artifacts:
  - notes/TRUE_CLIFFORD_BLOCK_MONOMIAL_LAMP_SUBSPACE.md
  - notes/TRUE_BLOCK_MONOMIAL_COORDINATE_COLLAPSE.md
---

# A trivial diagonal lamp subspace would embed W in a permutation ultraproduct

The complete argument is in `notes/TRUE_CLIFFORD_BLOCK_MONOMIAL_LAMP_SUBSPACE.md`.
In outline: Lemma 1 of the companion note gives
`‖A − B‖₂² ≥ 2 d_H(π(A), π(B))` for block-monomials, uniformly in the fiber
dimension and with no use of commutativity, so permutation parts form a
homomorphism `ϖ = π ∘ Θ : H_Cl → 𝒮_𝒰`; since `Θ(z) = −1` is scalar it factors
through `W = H_Cl/⟨z⟩`. The set `𝒮` of lamp words with diagonal image is a
`G`-submodule of `𝔽₂[G/Γ]`, closed under symmetric difference because
`(∏_S)(∏_T) = z^ε ∏_{SΔT}` with `z` scalar, and `G`-invariant because
block-monomials carry diagonals to diagonals. If `𝒮 = 0`, then tensoring with
a sofic representation of `G` — available since `G` is residually finite by
Kun–Thom Theorem E — gives a homomorphism `W → 𝒮_𝒰''` with kernel
`𝒮 = 0`, so `W` embeds in a permutation ultraproduct and is sofic. That
contradicts `wreath-not-sofic`, whence `𝒮 ≠ 0`.

This route requires `wreath-not-sofic` rather than restating Kun–Thom, so the
trust surface is inherited through that node and not duplicated. The remaining
inputs are the standard equivalence between embedding in `𝒮_𝒰` and soficity
(`Sofic/SoficUltraproduct.lean` with the separation-constant amplification of
`Sofic/SoficAmplification.lean`) and residual finiteness of `G` feeding
`Sofic/LEFSofic.isSofic_of_isLEF`.

**Scope.** The conclusion is a constraint on models, not a non-existence
result. It is strictly weaker than the abelian
`block-monomial-coordinate-collapse`, and the weakening is forced: the
Jordan–Wigner computation in the artifact exhibits `𝒮 ≠ 0` in the standard
Majorana representation, so no argument of this shape can refute block-monomial
Clifford models outright.
