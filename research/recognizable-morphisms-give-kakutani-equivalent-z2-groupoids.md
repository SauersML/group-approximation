---
rg: 2
id: recognizable-morphisms-give-kakutani-equivalent-z2-groupoids
kind: claim
title: A recognizable 2-dimensional morphism that is onto up to a shift is a Kakutani equivalence of Z^2 transformation groupoids (block origins form a full clopen transversal), so it preserves finite presentation of the crossed product and, between SFTs, quantum rigidity in both directions
distinct_from:
  labbe-full-group-embeds-in-its-supertile-corner: that is the self-map case for Labbé's own ω on Ω_U, used for full groups; this is the general statement for any recognizable morphism between two subshifts, used for crossed-product finite presentation and rigidity.
  recognizable-morphisms-collapse-quantum-rigidity-to-one-scale: that transports non-commuting operator families upward along a recognizable morphism at a fixed scale (target rigid implies source rigid, with explicit scales); this gives both directions at the level of the groupoid, with no scale bookkeeping.
  steinberg-fp-is-a-kakutani-invariant: that proves finite presentation is a Kakutani invariant; this supplies the Kakutani equivalences that substitutive structures produce.
---

**ESTABLISHED** through `recognizable-morphism-kakutani-equivalence-proof` (lane proof by bh-g2-abh,
2026-09-18). The proof is elementary and has not been reviewed. It is the standard supertile-transversal
argument, and no priority is claimed.

## Statement

Let `Y ⊆ B^(Z^2)` and `X ⊆ A^(Z^2)` be subshifts, and let `ω` be a 2-dimensional morphism in Labbé's
sense (arXiv:1808.07768, §2.7 and §2.9; recalled in `jeandel-rao-substitutive-structure-citation`).
It is defined on the language of `Y`, and every letter image is a nonempty rectangle. Assume two things:
- **recognizable in `Y`:** every point has at most one centered `ω`-representation;
- **onto up to a shift:** `X = ∪_k σ^k ω(Y)`.

Let `C = ω(Y)`. Write `G_Z = Z ⋉ Z^2` for transformation groupoids.
1. `C` is clopen and meets every orbit, and `ω: Y → C` is a homeomorphism.
2. **Groupoid isomorphism.** `(y, m) ↦ (ω(y), (W_y(m_1), H_y(m_2)))` is an isomorphism of topological
   groupoids `G_Y ≅ G_X|_C`. Here `W_y` and `H_y` are the cumulative widths along row 0 and heights along
   column 0 of the letter images. They are well defined because a 2-dimensional morphism gives
   horizontally adjacent letters images of equal height and vertically adjacent letters images of equal
   width.
3. **Finite presentation.** For every field `k`, `LC(Y, k) ⋊ Z^2` is finitely presented iff
   `LC(X, k) ⋊ Z^2` is. This follows from `steinberg-fp-is-a-kakutani-invariant`, item 2.
4. **Rigidity.** If `X` and `Y` are SFTs, `X` is quantum rigid iff `Y` is, by item 3(a) of the same node.
   If `Y` is an SFT and `X` is quantum rigid, then `X` is an SFT, directly from the recognizability
   structure (proof, Step 4).

Topological conjugacies and `GL_2(Z)`-conjugacies (`σ^(Mk) ∘ θ = θ ∘ σ^k`) are groupoid isomorphisms,
via `(x, k) ↦ (θx, Mk)`. So items 3 and 4 hold along any finite chain of such maps and morphisms.

## Lesson for general BH

- **Substitutive structure is rigidity-neutral.** Every recognizable desubstitution step, embedding and
  shear preserves the E2 question exactly, in both directions.
- **So the E2 question is a question about a Kakutani class.** Within that class one may choose the model
  with the needed geometry: an expansive direction for folding, a self-similarity for scale collapse, or a
  small tile set for search. Answering it for one model answers it for all.
- **What does change along the chain:** expansive and fault directions, and pattern sizes. The
  determinism obstructions of `determinism-closure-certifies-quantum-rigidity` are conjugacy invariant,
  but they are not claimed invariant under these non-uniform morphisms.

DERIVATION
recognizable-morphism-kakutani-equivalence-proof
