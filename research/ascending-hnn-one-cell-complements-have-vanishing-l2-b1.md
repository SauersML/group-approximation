---
rg: 2
id: ascending-hnn-one-cell-complements-have-vanishing-l2-b1
kind: claim
title: A one-cell complement whose group is an ascending HNN extension of a finitely generated group has vanishing first L²-Betti number and is aspherical
distinct_from:
  one-cell-complement-groups-have-vanishing-first-l2-betti: that is the open statement for every one-cell complement; this proves it when the group is an ascending HNN extension of a finitely generated group.
  non-ascending-one-cell-complements-have-vanishing-l2-b1: that is the open residual case, where the group is not such an extension; this is the proved case.
  lo-amenable-limit-one-cell-complements-are-aspherical: that proves vanishing for groups that are limits of left-orderable amenable groups; this uses an HNN structure instead.
artifacts:
  - research/artifacts/hl-one-cell-l2-2026-09-14.md
---

**ESTABLISHED** through `ascending-hnn-one-cell-l2-vanishing-proof`.

Let `L` be a finite connected contractible 2-complex, `e` an open 2-cell, `K = L − e` and
`G = π₁(K)`. Suppose that

  `G ≅ H *_σ = ⟨ H, t | t h t⁻¹ = σ(h), h ∈ H ⟩`

for a finitely generated group `H` and an injective endomorphism `σ : H → H`. Then
`b₁^(2)(G) = 0`, and `K` is aspherical.

## Special cases

- **Finitely generated commutator subgroup.** If `N = [G, G]` is finitely generated, then
  `G = N ⋊ Z` with `t` acting by an automorphism `σ`, so `G ≅ N *_σ`, and the claim applies.
  This covers free-by-cyclic one-cell complements.
- **No free subgroups.** `G` is finitely presented and maps onto `Z`. A finitely presented group
  without non-abelian free subgroups that maps onto `Z` is an ascending HNN extension of a finitely
  generated group (Bieri--Strebel; recalled, not pinned). So the claim covers every one-cell
  complement without non-abelian free subgroups. Amenable ones were already covered by
  `whitehead-one-cell-counterexamples-have-positive-first-l2-betti`, item 2.
- **Calibration.** `BS(1,2) = ⟨a, t | t a t⁻¹ = a²⟩` is a one-cell complement with `H = Z` and
  `σ = ×2` (`one-cell-complement-cyclic-cover-homology-is-finite`, Calibration). Its commutator
  subgroup `Z[1/2]` is not finitely generated, so the first special case does not reach it.

## Scope

In Bieri--Neumann--Strebel language, the hypothesis says that the abelianization character `φ` or
its negative lies in `Σ¹(G)`. That equivalence is recalled, not pinned, and the proof does not use
it. The complementary case is `non-ascending-one-cell-complements-have-vanishing-l2-b1`.

No novelty is claimed. The proof is the mapping-torus vanishing theorem of Lück's survey, applied
to a finite graph with a free-group lift of `σ`.
