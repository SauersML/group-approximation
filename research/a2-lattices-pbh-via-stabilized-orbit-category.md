---
rg: 2
id: a2-lattices-pbh-via-stabilized-orbit-category
kind: route
title: Take bh-groupoid's orbit category and host, split the rescaled category into strongly connected pieces, and apply the stabilized comparison to get a type (A) action
target: a2-lattices-satisfy-permutational-boone-higman
requires: [a2-lattices-embed-in-fp-simple-groups, degree-category-full-groups-stabilized-have-type-a-actions, boone-higman-type-a-class-closed-under-finite-extensions]
---

Notation as in `a2-lattices-embed-in-fp-simple-groups` (bh-groupoid).

**Step 1 (reduction).** The type-rotating subgroup has index at most 2, and `B_A`
passes to finite-index overgroups. So assume `Γ` type rotating, as in Step 0 there.

**Step 2 (the category and the embedding).** Steps 1–3 there give:
- the orbit category `ℭ_Γ`: finitely many objects (tile classes); left and right
  cancellative; units the finite stabilizers `K_a` in degree 0; (UFP*); locally
  finite;
- Li's groupoid `𝒢_Γ = I_l(ℭ_Γ) ⋉ ∂Ω` (Lemma 2.1);
- an injective homomorphism of `Γ` into its full group, after amplification and
  compression.
Step 5 there rescales degrees by `n` (with `3 | n` if `θ = 0`), embeds the full group
of `𝒢_Γ` in that of `𝒢_Γ^(n)` by the skew product over the phases, forms
`ℭ' = ℭ_Γ^(n) x B_2`, and proves `F(𝒢_Γ^(n) x G_2)` on the chosen object cylinders
`Y` is of type `F_∞` by Li's Theorem `thm:deg`.

**Step 3 (pieces).** By Step 4 there, each transition matrix `M_j` is irreducible. So
`ℭ_Γ` is strongly connected: already colour 1 joins any two objects. For the
rescaled category, write `a ⇝ b` if some morphism with target `a` and source `b` has
degree in `nN²`.
- `⇝` is reflexive and transitive.
- It is symmetric by the argument of Step 1 of
  `virtually-torsion-free-tree-lattices-pbh-via-kgraphs`. Given `λ : a ← b` of degree
  `nm` and any `μ : b ← a` of degree `e`, the morphism `(μλ)^(n-1)μ : b ← a` has degree
  `n e + n(n-1)m`, which lies in `nN²`.
So the objects of `ℭ_Γ^(n)`, and of `ℭ'`, split into pieces with no morphisms between
them, each strongly connected. Whichever object cylinders `Y` Step 5 uses, the
unit space is a union of these pieces intersected with `Y`.

**Step 4 (type (A)).** Apply `degree-category-full-groups-stabilized-have-type-a-actions`
with `ℭ = ℭ_Γ^(n)` and `Z = Y`.
- **Setting.** `ℭ_Γ^(n)` is finite, left cancellative and degree-graded with finite
  unit groups. It satisfies (UFP*), is locally finite, and splits into strongly
  connected pieces (Step 3).
- **Host.** The node's groupoid `𝒢'' = 𝒢_Γ^(n)|_Y x G_2` is exactly the host of Step 5
  there. Its full group is finitely presented, indeed `F_∞` (Step 2).
- **Conclusion.** The node gives a type (A) action of this full group on clopen sets,
  so the host lies in `B_A`. `Γ` embeds in it (Step 2), so `Γ ∈ B_A`, and the
  reduction of Step 1 finishes.
