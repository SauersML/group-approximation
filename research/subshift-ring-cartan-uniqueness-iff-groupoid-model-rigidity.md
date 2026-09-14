---
rg: 2
id: subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity
kind: claim
title: For an infinite minimal subshift X, Cartan uniqueness in LC(X,F_2)⋊Z is equivalent to rigidity of its effective groupoid models, and it gives ring and group flip rigidity at X
distinct_from:
  subshift-crossed-product-algebraic-cartans-are-conjugate: that open claim asks whether Cartan uniqueness holds; this proves what it is equivalent to and what it implies
  subshift-elementary-group-diagonal-iso-gives-flip-conjugacy: that proves diagonal-preserving rigidity for the groups; this reduces the ring half of the non-diagonal case to a groupoid statement
---

Let `X` be an infinite minimal subshift, `R_X = LC(X,F_2) ⋊_T Z`, `D_X = LC(X,F_2)` and `𝒢_X = Z ⋉ X`. "Algebraic
Cartan subalgebra" means the second member of an algebraic Cartan pair
(`algebraic-cartan-pairs-are-effective-groupoid-steinberg-algebras`).
1. `D_X` is an algebraic Cartan subalgebra of `R_X`.
2. For every algebraic Cartan subalgebra `B ⊆ R_X` there is a ring isomorphism `R_X ≅ A_{F_2}(G_B)` taking `B` onto the
   diagonal. Here `G_B` is effective, minimal, ample and Hausdorff, with Cantor unit space.
3. The following are equivalent:
   - (a) every algebraic Cartan subalgebra of `R_X` is `β(D_X)` for a ring automorphism `β`;
   - (b) every effective ample Hausdorff groupoid `G` with `A_{F_2}(G) ≅ R_X` as rings is isomorphic to `𝒢_X`.
4. If (a) holds, every infinite minimal subshift `Y` with `R_Y ≅ R_X` is flip conjugate to `X`.
5. Suppose (a) holds for `Y`, and every isomorphism `α: EL_3(R_X) → EL_3(R_Y)` has `α(GL_3(D_X)) = GL_3(B)` for an
   algebraic Cartan subalgebra `B ⊆ R_Y`. Then `EL_3(R_X) ≅ EL_3(R_Y)` implies `X` and `Y` are flip conjugate.

Over `F_2` discrete twists are trivial, because `F_2^× = {1}`. That removes the twist from the imported reconstruction.

Scope: this is a reduction. Whether (a) holds is OPEN (`subshift-crossed-product-algebraic-cartans-are-conjugate`). The
hypothesis of 5 is step (i) of Firewall F2 in `research/artifacts/sk-rigidity-intrinsic-reconstruction-2026-09-13-part1.md`.

Proof in `subshift-ring-cartan-uniqueness-reduction-proof`; details in
`research/artifacts/sk-rigidity-cartan-2026-09-13-part1.md` §1–§2.

**Review (sk-verify-5, 2026-09-13): PASS. Re-derived: trivial F_2-twists, compact metrizable unit space, minimality via the ideal I_U, no isolated points via a minimal idempotent and the socle, transport of the pair axioms along an F_2-linear isomorphism, full bisections giving [[T]], and item 5 via Theorem A.** See `research/artifacts/sk-review-5-2026-09-13-part3.md` §1.
