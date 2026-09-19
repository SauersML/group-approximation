---
rg: 2
id: mikaelian-rho-tau-shortcuts-fail-proof
kind: route
title: The ascending-ordered code distinguishes the two products
target: mikaelian-rho-tau-shortcuts-fail
requires: []
artifacts:
  - GroupApproximation/Higman/SequenceSpace.lean
  - GroupApproximation/Higman/OperationClosureRho.lean
---

## Complete argument

Let F = ⟨a,b,c⟩ be free, b_i = c⁻ⁱ b cⁱ, and for finitely supported
f : ℤ → ℤ let b_f = ∏_{i ∈ supp f, ascending} b_i^{f(i)} (the convention
of both Higman p. 469 and Mikaelian §2.3; in this repository
`SequenceSpace.elt` sorts the support ascending, and the rows b_i are a
free basis — `RowBasis.basisHom_injective`).  Take f = e₀ + e₁, so
b_f = b₀ b₁.

ρ.  The automorphism φ : a,b,c ↦ a,b,c⁻¹ sends b_i to b_{−i}, hence
φ(b_f) = b₀ b₋₁.  But ρf is supported on {−1, 0}, so b_{ρf} = b₋₁ b₀.
These are distinct elements of the free group on the rows.  Hence
φ(A_B) ≠ A_{ρB} in general (the a_f = a^{b_f} freely generate, so
distinct codes give distinct generators), and the printed clause
"A_{ρ(B)} = φ(A_B)" fails.

τ.  Here τf = f, so the printed claim "τ(b_f) = b_{f'}" with f' = f
asserts that the automorphism swapping b₀ and b₁ FIXES b₀ b₁; it sends
it to b₁ b₀ ≠ b₀ b₁.  The identification A_{τ(B)} = A_B^q at the end of
the clause inherits the failure.

σ, for contrast: i ↦ i+1 preserves the order of the support, so the
automorphism a,b,c ↦ a,b^c,c carries the ascending product to the
ascending product and the clause is correct — which is also why the
repository's σ closure is three lines while ρ needed an explicit flip
group (`FlipGroup`) and τ needs a genuine construction.

Higman's own proofs (Lemma 4.6) are unaffected: they act on the d-side
where, by his Lemma 4.2, a_f depends only on the weight vector of a
d-word and the order of the product never enters.  ∎
