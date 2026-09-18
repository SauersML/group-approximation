---
rg: 2
id: edge-split-ore-via-atom-plane-restriction
kind: route
title: The plane lemma and the atom-plane rearrangement together give common edge-split refinements in rank three
target: edge-split-operad-has-common-refinements
requires:
  - edge-splits-resolve-every-rational-plane
  - edge-split-dissections-respecting-an-atom-plane-split-there
---

Lane bh-free-54, 2026-09-18. This route covers `m = 2`.

1. **A common geometric refinement.** Given `D_1, D_2 ∈ 𝒪_E(Δ)`, apply
   `edge-splits-resolve-every-rational-plane` to the finitely many planes spanned by
   the faces of their pieces. This gives `D ∈ 𝒪_E(Δ)` refining both geometrically.
2. **Geometric refinement is operad refinement.** Suppose `D` refines `D' ∈ 𝒪_E(Δ)`
   geometrically. Induct on `|D'|`.
   - If `D'` is trivial, `D ≥_E D'`.
   - Otherwise write `D' = E_a ∘ (X, Y)`. Then `D` respects `E_a`'s plane, so by
     `edge-split-dissections-respecting-an-atom-plane-split-there`,
     `D = E_a ∘ (D_X, D_Y)` with `D_X, D_Y` edge-split in the halves' frames.
   - `D_X` refines `X` geometrically, and `D_Y` refines `Y`. By induction in the
     halves' frames (the statement is `GL_3(Z)`-equivariant), `D_X ≥_E X` and
     `D_Y ≥_E Y`. So `D ≥_E D'`.
3. **Conclusion.** Apply step 2 to `D_1` and to `D_2`. So `D ≥_E D_1, D_2`.
