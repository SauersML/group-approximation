---
rg: 2
id: hilbert-embeddable-length-lp-feasibility-proof
kind: route
title: Schoenberg detruncation, maximality of the word length, and the S3 character expansion
target: hilbert-embeddable-length-lp-feasibility
requires: []
artifacts:
  - notes/TRUE_GLEBSKY_HS_TRANSPORT_AUDIT.md
---

# Detruncation, maximality, and the S3 expansion

Direct establishment; the complete argument is §7 of the cited note.
`requires: []` is a proof commitment.

**Detruncation.** For `ψ ≥ 0` conditionally negative definite, `exp(−tψ)` is
positive definite (Schoenberg) and normalized at the identity, so `1 − exp(−tψ)`
is conditionally negative definite. Apply with `ψ = d(1,·)` and `t = 1/n`, and
compare values: `1 − e^{−1/n} ≤ 1/n` on the defect set, and `1 − e^{−d/n} ≥
1 − e⁻¹` once `d ≥ n`.

**Maximality.** An invariant length is subadditive and constant on conjugacy
classes, so `ℓ(x₁^{g₁}···x_k^{g_k}) ≤ Σ ℓ(x_i) ≤ k·max_X ℓ`. Taking the
shortest such expression gives `ℓ ≤ max_X ℓ · d(1,·)`, and `d(1,·)/n` is itself
an admissible invariant length, so it is the pointwise maximum.

**The `S₃` expansion.** Classes `{e}`, the three transpositions, the two
3-cycles; irreducibles `1`, `sgn`, `χ` with `χ(e) = 2`, `χ(τ) = 0`,
`χ(σ) = −1`. The word metric of the transposition class takes values `0, 1, 2`.
Solving `a + b + 2c = 0`, `a − b = 1`, `a + b − c = 2` gives `c = −2/3`,
`a = 7/6`, `b = 1/6`. The coefficient on the nontrivial character `sgn` is
positive, so the kernel is not conditionally negative definite. Identifying
this metric with the `𝔽₂`-rank length on `GL₂(𝔽₂) ≅ S₃` — `rank(g−1)` is `1`
on transvections and `2` on the order-3 elements — reproduces the calibrating
failure already recorded in `hilbert-embeddable-length-hyperlinearity` and
shows it lies in Glebsky's family.

**Linearity of the constraints.** Class functions on `H` form a finite
dimensional real vector space with the irreducible characters as a basis;
conditional negative definiteness of `(a,b) ↦ ℓ(a⁻¹b)` for an invariant `ℓ`
with `ℓ(1) = 0` is equivalent to nonpositivity of the coefficients at
nontrivial irreducibles, which is a system of linear inequalities in that
basis. Subadditivity, the defect bound and the separation bound are linear
by inspection.
