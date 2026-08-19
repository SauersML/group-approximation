---
rg: 2
id: positive-core-bernoulli-ce-proof
kind: route
title: Separable positive stabilizers give Schreier approximations, then GKP Theorem A
target: positive-core-bernoulli-ce
requires: []
artifacts:
  - notes/FALSE_POSITIVE_CORE_IS_SOFIC.md
  - research/artifacts/kun-thom-2608-06222-verified.md
---

# Separable positive stabilizers, then GKP Theorem A

Import of a complete argument already in the corpus. The full proof —
`(PCS1)`–`(PCS17)`, four sections — is `notes/FALSE_POSITIVE_CORE_IS_SOFIC.md`,
dated 2026-08-12. `requires: []` is a proof commitment, not a placeholder.

The chain: Suslin stability gives `E_r(R_ℓ) = SL_r(R_ℓ)` and identifies each
positive stabilizer `H_ℓ = ℓΓℓ⁻¹` as the elementary group of a polynomial ring
on the columns of `ℓ`; degree truncation `Q_N = R₊/I_N` separates `H_ℓ` in `Γ`
by finite ring congruences; separability plus residual finiteness gives exact
finite Schreier approximations on each orbit, and `X₀` is a countable union of
orbits, so `Γ ↷ X₀` is a sofic action; Gao–Kunnawalkam Elayavalli–Patchell
Theorem A then makes `W₀ = (⊕_{X₀} C₂) ⋊ Γ` sofic, and its left regular
representation embeds `N₀` in a tracial matrix ultraproduct.

## Provenance and the filename

The artifact carries a `FALSE_` prefix, which in this corpus marks the *lane* a
file belongs to — here the full-compression-semigroup dilation lane, which is
refuted — not the truth of its contents. The contents are positive and were
read end to end before import: the document has no retraction, no caveat
paragraph, and closes by stating the surviving endpoint question rather than
withdrawing the result. Importing across that prefix is exactly the kind of
thing that can launder a false claim, so it is flagged here rather than left
implicit.

## External input, and it is already verified here

The one external theorem is GKP Theorem A, which the artifact cites by name.
It is transcribed verbatim in
`research/artifacts/kun-thom-2608-06222-verified.md` from the authors' own
arXiv source: *"Let G, H be sofic groups, α: H ↷ X be a sofic action. Then the
generalized wreath product G ≀_α H is sofic."* Note that this is the same
theorem `coordinate-action-not-sofic-proof` runs in contrapositive against the
full coset action. Both nodes stand or fall with it together, and it is the
one place in this subtree where a single external statement carries weight in
two opposite directions — worth knowing if it is ever revised.

Suslin stability and residual finiteness of the pair are standard and are also
recorded in the artifact (`(PCS7)`, `(PCS8)`).
