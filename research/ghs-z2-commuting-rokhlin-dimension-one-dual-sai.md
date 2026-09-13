---
rg: 2
id: ghs-z2-commuting-rokhlin-dimension-one-dual-sai
kind: claim
title: Gardella–Hirshberg–Santiago - commuting-tower Rokhlin dimension one of a Z_2-action is a central equivariant circle, makes the dual strongly approximately inner, and forces the Rokhlin property on O_2 and on M_(2^∞)-absorbing algebras
distinct_from:
  bemsw-outer-z2-kirchberg-rokhlin-dimension-at-most-one: that imports the bound without commuting towers for every outer Z_2-action on a unital Kirchberg algebra; this imports what the commuting-tower version gives and where it forces the Rokhlin property.
  outer-actions-on-o2-kk-g-contractible-iff-rokhlin: that proves Rokhlin iff KK^G-contractible on O_2 and, in item 5, that finite commuting-tower dimension on O_2 forces the Rokhlin property; this imports the published statement of that item 5 (Proposition 3.32 here) and the Z_2 dimension-one dual form.
---

**ESTABLISHED (literature).**  E. Gardella, I. Hirshberg and L. Santiago,
*Rokhlin dimension: duality, tracial properties, and crossed products*,
arXiv:1709.00222, read from the PDF text on 2026-09-13.

1. **Corollary 3.27.**  For a unital `A` and `α : Z_2 ↷ A`,
   `dim_Rok^c(α) ≤ 1` iff there is a unital equivariant \*-homomorphism
   `(C(S^1), Lt) → (A_∞ ∩ A', α_∞)`.  If `dim_Rok^c(α) = 1`, every such map is
   injective.
2. **Proposition 3.32.**  For a finite group `G` and any action
   `α : G ↷ O_2` with finite Rokhlin dimension with commuting towers, `α` has the
   Rokhlin property.  The authors note that the conclusion fails if only
   `dim_Rok(α) < ∞` is assumed.
3. **Definition 3.33.**  For `G` finite abelian and `B` unital, `β` is strongly
   approximately inner if there are unitaries `v_g ∈ (B^β)_∞` with
   `β_g(b) = v_g b v_g*` for all `b` and `g`.  They attribute it to
   Definition 3.6 of their reference [38].  This matches the definition recorded in
   `izumi-rokhlin-approximately-representable-duality`.
4. **Theorem 3.34.**  Let `A` be separable and unital, `α : Z_2 ↷ A`, with
   `dim_Rok^c(α) ≤ 1` and `A ≅ A ⊗ M_(2^∞)`.  Then `α` has the Rokhlin property.
   - *Mechanism of the proof:* the image `w` of the canonical unitary of `C(S^1)`
     satisfies `w* u w = −u = α̂(u)` and `w* a w = a`.  So `Ad(w*) = α̂`, and
     `α̂` is strongly approximately inner.
   - Approximate representability of `α̂` then follows through `M_(2^∞)`-absorption
     and their reference [38], Lemmas 3.8 and 3.10.
5. **Limits stated by the authors.**
   - After Theorem 3.34: it is not enough to assume `dim_Rok(α) ≤ 1` (Remark
     3.18(a)).
   - Before it: they do not know whether the conclusion holds under
     `dim_Rok^c(α) < ∞`, or for general finite abelian groups.
6. **Remark 3.18(c).**  Whether finite Rokhlin dimension preserves the UCT for
   nuclear algebras is equivalent to the UCT problem.  Their reason: Barlak's
   reduction to pointwise outer finite group actions on `O_2`, all of which have
   Rokhlin dimension at most one.

**Credit.**  Item 5 of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin` is
Proposition 3.32 of this paper in the case `A = O_2`.  The route there is a
separate derivation; the published statement predates it.

Citation: `ghs-z2-commuting-rokhlin-dimension-one-dual-sai-citation`.
