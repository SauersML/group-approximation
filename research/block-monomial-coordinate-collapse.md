---
rg: 2
id: block-monomial-coordinate-collapse
kind: claim
title: Block-monomial fiber models collapse to permutation models
invalidates: [block-monomial-fiber-models]
distinct_from:
  coordinate-action-not-sofic: that says the coset action is not sofic, imported by citation; this is a proved reduction sending a strictly larger class of models — block-monomial, not permutation — into that citation's reach
  diagonal-normalizer-rigidity: that concerns approximate normalizers of the FULL diagonal masa and is sharp there; this concerns exact block-monomiality over a COARSE decomposition, which that result explicitly does not cover
artifacts:
  - notes/TRUE_BLOCK_MONOMIAL_COORDINATE_COLLAPSE.md
  - research/artifacts/kun-thom-2608-06222-verified.md
---

No *block-monomial fiber model* of `M_KT = L(W)` exists: no trace-preserving
embedding `Θ : M_KT → ∏_𝒰 M_{d_n}` with `d_n = |Y_n|·m_n`, lamps in
`∏_𝒰(D_{Y_n} ⊗ 1)`, and every `Θ(u_g)` represented by matrices that are
block-monomial over `Y_n` (permutation of `Y_n` with arbitrary `U(m_n)`
blocks). The fiber dimension `m_n` is unconstrained.

The proof is three moves. A block-monomial matrix has a permutation part, and
`‖A − B‖₂² ≥ 2 d_H(π(A), π(B))` uniformly in `m` — a mismatch of permutation
parts moves a whole block, so growing the fiber dilutes traces but not
mismatches. Hence multiplicativity of `Θ` descends to the permutation parts and
`σ : G → 𝒮_𝒰` is a homomorphism, covariant for the lamps because conjugating a
coarse diagonal by a block-monomial cancels the blocks exactly. `σ` need not be
faithful — that is precisely what the fiber was meant to buy — but faithfulness
is bought back for free by tensoring with a sofic representation of `G`, which
exists because `G` is residually finite. The result is a genuine sofic-action
witness, contradicting Kun–Thom Corollary D.

**What this closes.** The most natural reading of "the trace is blind to
sizes": put the lamps on coordinates, hide the group's Hilbert–Schmidt
separation in a growing unitary fiber, and escape Corollary D because the group
unitaries are no longer permutations. The trace is indeed blind to the fiber.
The obstruction is not in the fiber — it rides on the lamps, and the lamps are
faithfully represented on the coordinates whatever the fiber does. Recorded as
`block-monomial-fiber-models`, now invalidated.

**Why it is not covered by `diagonal-normalizer-rigidity`.** That result needs
the **full** diagonal masa, and says so: for a merely coarse subalgebra the
Fourier-block unitary `⊕_j F_{m}` centralizes it while sitting at distance `√2`
from every monomial, so no monomial approximation is available. This claim
shows that gap is not a door. A Fourier-block unitary is still block-monomial
over the coarse index set; its permutation part is still defined and still
multiplicative; the lamps still ride on the coarse coordinates. Distance from
monomials was never the relevant measurement — existence of a permutation part
was.

**Scope, and it is a real scope.** Step 1 uses block-monomiality *exactly*, in
the ultraproduct. Models whose group unitaries are only approximately
block-monomial, with a defect bounded away from zero, are untouched — and that
is the generic case, since a finite window of the lamp algebra has `2^k` atoms
of equal trace, giving an approximate coarse decomposition whose defect is
governed by the boundary of the window in `G/Γ`, which carries a constant
fraction of the mass because property (T) and infinite index leave no Følner
sets. Theorem 2 kills exact block structure; amplification
(`notes/OBSTRUCTIONS.md` §3) kills the naive approximate one. Nothing here says
`M_KT` is not Connes-embeddable.
