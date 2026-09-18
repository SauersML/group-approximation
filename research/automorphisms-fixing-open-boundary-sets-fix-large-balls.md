---
rg: 2
id: automorphisms-fixing-open-boundary-sets-fix-large-balls
kind: claim
title: An automorphism of a thick Euclidean building that fixes an open set of chambers at infinity fixes an apartment and balls of every radius pointwise
distinct_from:
  euclidean-building-lattices-lie-in-permutational-bh-class: that gets effectiveness of lattice actions from Ciobotaru--Le Bars topological freeness; this proves the pointwise statement for a single automorphism, with no discreteness, so it applies factorwise to lattices in products.
---

**ESTABLISHED** through `open-boundary-fixers-fix-balls-proof` (lane proof; not
independently reviewed; no priority claimed). Inputs:
- standard building theory with the complete apartment system (Abramenko--Brown,
  Ch. 11; not re-read);
- density of the chambers opposite a given one (Ciobotaru--Le Bars, arXiv:2601.13092,
  Corollary `cor opp dense`, as read at source by bh-groupoid; not re-read here).

**Statement (Lemma H).** Let `X` be a locally finite thick Euclidean building, or a
locally finite leafless tree with more than two ends. Let `h ∈ Aut(X)`, not assumed to
preserve types or to lie in a discrete group. Suppose `h` fixes every chamber of a
nonempty open set `U` of chambers at infinity (cone topology). Then:
1. `h` fixes pointwise every apartment `A(C_1, C)` spanned by a chamber `C_1 ∈ U` and a
   chamber `C ∈ U` opposite to it;
2. `h` fixes pointwise balls of every radius.

**Consequence (effectiveness in products).** Let `Γ` act on `X = X_1 x ... x X_m`
(each `X_i` as above) with finite vertex stabilizers, finitely many vertex orbits and
trivial kernel. If `g ∈ Γ` fixes pointwise a nonempty open subset of `∏ Ch(∂X_i)`,
then `g = 1`.
- Such a set contains a product of open sets, so each coordinate of `g` fixes balls
  of every radius in its factor (item 2).
- So `g` fixes pointwise balls of every radius in `X`.
- For each vertex `z`, the fixators of the balls around `z` form a decreasing chain in
  the finite group `Stab_Γ(z)` with trivial intersection, so the chain reaches `1`.
  Finitely many vertex orbits make the radius uniform.
So the transformation groupoid of `Γ` on `∏ Ch(∂X_i)` is effective.
