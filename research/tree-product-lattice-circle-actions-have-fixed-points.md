---
rg: 2
id: tree-product-lattice-circle-actions-have-fixed-points
kind: claim
title: Every circle action of a perfect lattice with dense projections in a product of two boundary-2-transitive tree groups has a global fixed point
distinct_from:
  higher-rank-p-adic-lattices-are-not-left-orderable: that imports non-left-orderability for lattices in algebraic p-adic groups; this proves circle rigidity for lattices in products of possibly non-algebraic tree groups, one of the inputs a Deroin–Hurtado argument for those lattices needs
---

**ESTABLISHED (unreviewed).** Let `T_1`, `T_2` be locally finite trees and let
`G_i ≤ Aut(T_i)` be closed, non-compact and 2-transitive on `∂T_i`. Let `Γ ≤ G_1 × G_2` be a
lattice whose projections to `G_1` and to `G_2` are dense, and assume `Γ` is perfect. Then every
homomorphism `ρ : Γ → Homeo_+(S^1)` has a global fixed point.

**Scope.**

- It applies to the simple finite-index subgroups of the Burger–Mozes lattices in
  `U(A_(2n)) × U(A_(2m))` (`burger-mozes-infinitely-transitive-tree-groups`, items 1, 4, 5).
- It is the circle-rigidity input (Witte Morris, arXiv:2407.09742v1, Theorem 2.4(3), used in
  Theorem 4.1(2) and Proposition 4.19) that transcribing the Deroin–Hurtado proof to
  `irreducible-tree-product-lattices-are-not-left-orderable` requires. See §3 of
  `research/artifacts/zp-tree-lattice-left-orderability-2026-09-13.md` (gap G7).
- It says nothing about actions on the line. A line action compactifies to a circle action
  with a fixed point at infinity.

**Credit.** It is a direct application of Burger's Corollary 1.9 (arXiv:0905.0136), which
Burger attributes to [25] and to Bader–Furman–Shaker, together with the Burger–Mozes structure
theory of tree groups. It is not claimed as new.

Proof: route `tree-product-lattice-circle-actions-have-fixed-points-proof`.
