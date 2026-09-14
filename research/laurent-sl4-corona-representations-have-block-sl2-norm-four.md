---
rg: 2
id: laurent-sl4-corona-representations-have-block-sl2-norm-four
kind: claim
title: Every corona representation of SL_4(F_q[t^±1]) gives the block SL_2 Laplacian norm four
distinct_from:
  sl4z-corona-representations-have-block-sl2-norm-four: that is the characteristic-zero crux for SL_4(Z); this is the positive-characteristic crux at the Laurent lattice inside every G_X, where unipotents are torsion and finite-dimensional representations are congruence without superrigidity.
  laurent-sl4-matricially-stable: that asks every asymptotic homomorphism to be near a genuine representation; this asks only that the block SL_2 Laplacian keep norm four, which stability implies.
  laurent-sl4-block-sl2-norm-four-off-full-unipotent-spectrum: that settles the norm conclusion off the full-spectrum case; this is the whole crux, equivalent to its full-spectrum case.
artifacts:
  - research/artifacts/sk-mf-laurent-2026-09-14-part1.md
---

**OPEN.** Let `A = F_q[t,t^{-1}]`, `Λ = SL_4(A)`, and `z = S+S^{-1}+T+T^{-1}` for free `S, T ∈ SL_2(F_q[t])` in the
upper-left block. Every unital *-homomorphism `π : C*(Λ) → ∏_n M_{k_n}/⊕_n M_{k_n}` satisfies `‖π(z)‖ = 4`.

**Consequences.**
- It implies that `C*_r(Γ)` is not MF for every countable `Γ ⊇ Λ`, in particular for every `G_X` (route
  `subshift-el-reduced-not-mf-from-laurent-corona-norm-four`).
- It is implied by `laurent-sl4-matricially-stable` (route `laurent-corona-norm-four-from-matricial-stability`), so it is
  a weaker crux for the same root.

## Attempts

- **Congruence side.** Done: `laurent-sl4-block-sl2-norm-four-off-full-unipotent-spectrum`.
  - If the joint spectrum of the column unipotent `A^3` is not all of `Â^3`, the representation factors through some
    `SL_4(A/J)` and has norm 4 (`laurent-unipotent-spectra-are-finite-or-full`).
  - So the claim is equivalent to its full-spectrum case, which contains every MF embedding.
- **Averaging at zero-annihilator characters.** Expected dead, by the positive-characteristic analogue of
  `mdls-averaging-at-non-torsion-character-gives-spectral-gap`. Averaging a spectral piece at a character with zero
  annihilator over the block `SL_2(A)` gives a representation weakly contained in `λ_{SL_2(A)}`. Not written out.
- **Far-level spectral projections.** Open.
  - Clopen cylinder projections for finite `F ≤ A^3` exist in `σ(C*(A^3))`, and the stabilizer of a level-`J`
    character contains `SL_3(A,J)`.
  - The finite average needs invariance under `SL_2(A,J)` in the block, which a representation that factors through no
    `SL_4(A/J)` does not supply. This is the same wall as for `SL_4(Z)`.
