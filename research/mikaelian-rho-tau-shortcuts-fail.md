---
rg: 2
id: mikaelian-rho-tau-shortcuts-fail
kind: claim
title: Mikaelian's free-group shortcuts for the reversing and swap closures fail on a two-letter witness
distinct_from:
  hnn-torsion-theorem: unrelated permanence lemma; this claim is a literature erratum about two closure clauses in the modified Higman proof.
artifacts:
  - GroupApproximation/Higman/OperationClosureRho.lean
  - GroupApproximation/Higman/OperationClosureTau.lean
  - GroupApproximation/Higman/SequenceSpace.lean
---

In V. Mikaelian, "A modified proof for Higman's embedding theorem"
(arXiv:1908.10153v8), §4, the clauses "S is closed under ρ" and "S is
closed under τ" are defective as printed.  Both attempt to transfer
benignness inside the rank-three free group by an automorphism — for
ρ the map a,b,c ↦ a,b,c⁻¹ (so b_i ↦ b_{−i}), for τ the automorphism of
the free row group swapping b₀ and b₁ — and both assert that this
carries b_f to b_{ρf} (resp. b_{τf}).  The coded word b_f is, by the
paper's own §2.3 (and Higman's p. 469), the ASCENDING-ordered product
∏ b_i^{f(i)} over non-commuting rows.  Minimal witness, f(0) = f(1) = 1:
for ρ, φ(b_f) = b₀b₋₁ while b_{ρf} = b₋₁b₀; for τ, f' = f so the claim
says the swap fixes b₀b₁, but the swap sends it to b₁b₀.  Since the a_f
freely generate (the paper's own observation), the subgroups differ
and neither identification holds.  The same witnesses were found
independently, kernel-checked, in this repository's coding
(`OperationClosureRho`, `bElt_tauSeq`), where the true relations carry
an inversion (ρ) and an adjacent-syllable transposition (τ).

What is NOT in question: Higman's theorem and his own proofs of both
clauses, which run on the d-side through the weight-only property
(Lemma 4.2: a_f depends only on the weight vector of a d-word, because
a is centralized exactly by the derived group of ⟨d_i⟩), where order is
irrelevant; and the σ shortcut, which is valid precisely because
i ↦ i+1 is order-preserving on the index set.  Consequences for the
formalization: ρ and τ are d-side-or-bespoke with no correct cheap
free-group route in either source; the repository's FlipWitness is the
primary ρ route; and for the apparatus, Mikaelian's explicit tower
Λ₀ = K₀ ∗_{L₀} t, Λ₁ = K₁ ∗_{L₁} s, Θ = Λ₀ ∗_F Λ₁, Ψ = Θ ∗_ω d,
Δ = Ψ ∗_δ e (his (4.2) reproducing Higman's d-relations) is the better
Lean target than Higman's Lemma 4.1, every step being a named HNN
extension or amalgam.  Notation trap: in his ω_m paragraph the shift
automorphism a,b,c ↦ a,b^c,c is called "ρ".

Found 2026-08-21 by the formalization fleet (the witness by the ρ/τ
implementer; the source reading by the literature verifier; the
convention check at Higman p. 469).
