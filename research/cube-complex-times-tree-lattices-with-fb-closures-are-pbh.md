---
rg: 2
id: cube-complex-times-tree-lattices-with-fb-closures-are-pbh
kind: claim
title: A virtually torsion-free group acting geometrically on (CAT(0) cube complex) × (tree) lies in the permutational Boone--Higman class when the closure of its projection to the cube-complex factor has no open subgroup fixing a point at infinity
distinct_from:
  cat0-groups-with-a-tree-factor-lie-in-type-a-class: that reduces Y × T lattices to a faithful member of BS_G for the fibre G; this supplies that member for every cube-complex factor Y from one geometric condition on the closure of the Y-projection.
  cat0-groups-on-symmetric-space-times-tree-lie-in-type-a-class: that treats symmetric-space factors through Borel density; this treats locally finite CAT(0) cube complex factors (products of trees included) through bounded fixed sets.
  three-tree-lattices-escape-only-via-discrete-normal-subgroups: that asks trivial quasi-centre of single-tree closures Ḡ_k; for Y = T_i × T_j this asks (FB) of the pair closure instead, a different sufficient condition.
---

**ESTABLISHED** through `cube-complex-times-tree-fb-closures-pbh-proof` (lane proof,
elementary; not independently reviewed; no priority claimed).

**Setting.** `Y` is a locally finite CAT(0) cube complex and `T` a locally finite
tree. `Γ` is virtually torsion-free and acts properly and cocompactly on `Y × T`.
Fix a torsion-free finite-index `Γ_0` preserving the product decomposition. Let
`L` be the closure of `pr_Y(Γ_0)` in `Aut(Y)`.

**Theorem.** If `L` satisfies (FB) of
`cubical-hecke-members-faithful-when-closure-fixes-bounded-sets` (no open subgroup
of `L` fixes a point of `∂Y`), then `Γ ∈ B_A`. So `Γ` and all its subgroups embed
in finitely presented simple groups.

**Necessary side condition.** By item 4 of the same node, (FB) can hold only if the
fibre `G = Stab_(Γ_0)(v)` (`v` a vertex of `T`) is residually finite.
Non-residually-finite fibres are exactly the case this method cannot reach.

**Instances.**
- **(a) Lattices on three trees, pair closures.** `Y = T_i × T_j`, `T = T_k`: a
  three-tree lattice lies in `B_A` whenever the closure of its projection to
  `Aut(T_i) × Aut(T_j)` satisfies (FB), for some ordering. This complements
  `three-tree-lattices-escape-only-via-discrete-normal-subgroups`, which asks for
  trivial quasi-centre of single-tree closures.
- **(b) Dense projections.** If `pr_Y(Γ_0)` is dense in `Aut(Y)` and `Aut(Y)`
  satisfies (FB), then `Γ ∈ B_A`. `Aut(Y)` satisfies (FB) for `Y` a product of
  regular trees of degree at least 3 (fixators of balls fix only those balls).
- **(c) Cube-complex fibres beyond trees and symmetric spaces.** For instance `Y`
  the universal cover of a compact special cube complex, with `Γ` an irreducible
  lattice on `Y × T` (these need not be virtually special). The fibre is then
  virtually special, hence residually finite, so the side condition holds, and
  (FB) for `L` is the only remaining input. Whether such irreducible lattices exist
  for a given `Y` is not addressed here.

**Scope.** The case where `pr_Y(Γ_0)` has non-discrete closure with an open
subgroup fixing a point at infinity is not covered.
