---
rg: 2
id: glebsky-hs-transport-step-classification-proof
kind: route
title: Read both Glebsky papers and exhibit the system that blocks the universal solution
target: glebsky-hs-transport-step-classification
requires: []
artifacts:
  - notes/TRUE_GLEBSKY_HS_TRANSPORT_AUDIT.md
---

# Read both Glebsky papers and exhibit the blocking system

Direct establishment; the complete argument is §§1–2 and §5 of the cited note.
`requires: []` is a proof commitment.

The classification of steps 1, 2, 5, 6 as type (a) is a reading of the proofs
plus the standard fact that a metric approximation property is determined by
finite subsets, hence passes to subgroups and to residual limits
(Alekseev–Bradford Remark 3.3 states the finite-subset dependence).

The classification of step 3 as type (b) is the hypothesis `K ⊆ Fin` printed in
Corollary 19 of arXiv:1506.06940, together with the observation that the
converse half of that paper's Lemma 3 — the half that manufactures an invariant
length from an algebraic separation condition — is the only bridge from the
length-free notion (Definition 6) back to the metric notion (Definition 3).
The easy half of Lemma 3 does survive for `(U(n), ‖·‖₂)`, because the
normalized Hilbert–Schmidt length is invariant and subadditive
(`‖uv−1‖₂ ≤ ‖u−1‖₂ + ‖v−1‖₂`), so `n`-consequences of the `ε`-ball lie in the
`nε`-ball. Only the manufacturing direction fails, and it fails because the
length is prescribed rather than chosen.

The refutation of step 4 is the explicit system `x²a⁻¹`, together with the
observation that `ℤ/2` is a quotient of the auxiliary finite group
`D_N ⋊ G_N = (∏_{M ∈ M_N}(H^{G_M})^m) ⋊ G_N` whenever the lamp `H` is `ℤ/2`.

Sources read from the PDF on 2026-08-14: arXiv:1910.08631 in full; and from
arXiv:1506.06940 the Definitions 1–8, Lemma 3, Propositions 1, 4, 5, 17,
Corollaries 6, 7, 19, Theorem 16, Proposition 20. The DGLT norm conventions are
§1.2 of arXiv:1711.10238, read directly.
