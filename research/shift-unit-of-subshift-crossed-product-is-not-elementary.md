---
rg: 2
id: shift-unit-of-subshift-crossed-product-is-not-elementary
kind: claim
title: The shift unit of LC(X,k)⋊Z is not an elementary matrix product in any rank, so the acting group does not sit diagonally in EL_n
---

**ESTABLISHED (unreviewed).** Let `X ⊆ A^Z` be a nonempty subshift, `k` a field, `R = LC(X,k) ⋊ Z`, and `n ≥ 1`.
Then `diag(u,1,…,1) ∉ E_n(R)`.

The half-line compression index `a ↦ ind(PaP)` is a homomorphism `GL_n(R) -> Z`. It vanishes on elementary matrices
and equals `−1` on `diag(u,1,…,1)`.

**Firewall.** Embedding the acting group `Γ` in `EL_n(LC(X,k) ⋊ Γ)` by `γ ↦ diag(u_γ,1,…,1)` needs `Γ` to act by
products of commutators of units.
- For `Γ = Z`, use `t ↦ diag(u^t, u^(-t), 1)` (Whitehead) instead.
- For nonabelian `Γ`, the map `γ ↦ diag(u_γ, u_γ^(-1), 1)` is not a homomorphism: the product is
  `diag(u_(γδ), u_(δγ)^(-1), 1)`.
- Hence the overgroup step `rf-groups-lie-in-derived-subgroups-of-rf-groups`.

Route: `shift-unit-of-subshift-crossed-product-is-not-elementary-proof`.

**Review (sk-verify-3, 2026-09-13): PASS.** Orbit representation, the algebraic Fredholm index as a homomorphism, its vanishing on elementary matrices (`N² = 0`) and index −1 for the shift re-derived. See `research/artifacts/sk-review-3-2026-09-13-part3.md` §A1.

**Review (sk-verify-4, 2026-09-13): PASS, independent concurrence.** Orbit representation, the Fredholm property of PaP, additivity of the algebraic index, zero index of elementary matrices, and index −1 of the shift re-derived. See `research/artifacts/sk-review-4-2026-09-13-part1.md` §1.
