---
rg: 2
id: laurent-sl4-block-sl2-norm-four-off-full-unipotent-spectrum
kind: claim
title: A representation of SL_4(F_q[t^±1]) whose column unipotent spectrum is not full gives the block SL_2 Laplacian norm four
distinct_from:
  sl4z-block-sl2-norm-four-unless-unipotent-spectrum-is-full: that is the same statement for SL_4(Z) through the torus dichotomy; this is the positive-characteristic Laurent lattice inside every G_X, through the window-density dichotomy and the chain-ring invariant vectors.
  laurent-sl-n-representations-have-sl2-invariant-vectors: that is the finite-dimensional theorem; this extends its norm conclusion to every unital C-star representation with non-full column unipotent spectrum, including infinite-dimensional and corona ones.
  laurent-sl4-corona-representations-have-block-sl2-norm-four: that is the open crux for all corona representations; this settles it exactly off the full-spectrum case.
artifacts:
  - research/artifacts/sk-mf-laurent-2026-09-14-part1.md
---

**ESTABLISHED (unreviewed).** Let `A = F_q[t,t^{-1}]`, `Λ = SL_4(A)`, and `σ : C*(Λ) → B` a unital *-homomorphism into a
unital C*-algebra. Suppose the joint spectrum of `σ(I + v_1 e_14 + v_2 e_24 + v_3 e_34)`, `v ∈ A^3`, is not all of
`Â^3`. Let `S, T ∈ SL_2(F_q[t])` generate a free group, placed in the upper-left block, and
`z = S+S^{-1}+T+T^{-1}`. Then `‖σ(z)‖ = 4`. If `B = B(H)`, the block `SL_2(A)` fixes a nonzero vector.

**What it does for the crux.**
- `laurent-sl4-corona-representations-have-block-sl2-norm-four` holds off the full-spectrum case, so it is equivalent to
  that case.
- Every MF embedding of `C*_r(Λ)` has Haar, hence full, column unipotent spectrum. So the congruence mechanism, extended
  here from finite-dimensional to arbitrary representations, reaches none of the maps the MF question is about. This is
  exactly the `SL_4(Z)` situation.

**Model tests.**
- The regular representation has full spectrum and `‖λ(z)‖ = 2√3 < 4` (Kesten), so the hypothesis cannot be dropped.
- The trivial representation has spectrum `{1}` and norm 4.

Proof: `laurent-sl4-block-sl2-norm-four-off-full-spectrum-proof`.

## Review
- **sk-verify-18 PASS (2026-09-14, `research/artifacts/sk-verify-18-2026-09-14-part7.md`):** re-derived: congruence factoring by Corollary A′; isometry on a surviving simple summand; the chain-ring node covers every finite commutative principal ideal ring and the same upper-left block SL_2, so ρ(z) has eigenvalue 4. Freeness of S, T is used only in the Kesten model test.
