---
rg: 2
id: some-simple-lattice-in-a-product-of-trees-is-left-orderable
kind: claim
title: Some torsion-free simple cocompact lattice in a product of two trees is left-orderable
distinct_from:
  higher-rank-real-lattices-are-not-left-orderable: that imports non-left-orderability of lattices in real semisimple Lie groups of real rank at least two; this asks for a left-orderable simple lattice in a product of two locally finite trees, where the ambient group is totally disconnected and the lattice need not be linear
---

There are locally finite trees `T_1`, `T_2` and a cocompact lattice
`Γ ≤ Aut(T_1) × Aut(T_2)` that is torsion-free, simple and left-orderable.

Such a `Γ` is of type F, so this claim answers Zaremsky Problem 1.22 affirmatively:
route `some-left-orderable-simple-group-has-type-f-via-burger-mozes`.

**Existence of the lattices.** Burger–Mozes, *Lattices in product of trees*, give for
every one-vertex VH-T-complex `Z` a one-vertex VH-T-complex `X ⊇ Z` whose fundamental
group is a virtually simple irreducible cocompact lattice in `U(A_(2n)) × U(A_(2m))` with
dense projections (`burger-mozes-infinitely-transitive-tree-groups`, item 5). Its
finite-index simple subgroup is again a torsion-free cocompact lattice.

**Facts about any such `Γ`.**

- `Γ` acts on `T_1` with vertex stabilizers that act freely and cocompactly on `T_2`. So
  `Γ` is the fundamental group of a finite graph of finitely generated free groups whose
  edge groups have finite index in the adjacent vertex groups.
- `cd Γ ≤ 2`. So in any faithful action of `Γ` on `R`, at most two nontrivial elements have
  pairwise disjoint supports (`finite-cd-line-groups-bound-disjointly-supported-families`).
- `Γ` is irreducible. It has no proper finite-index subgroup, so a reducible `Γ` would
  itself be a direct product of lattices in the two factors. Simplicity would force one
  factor to be trivial, and the other factor alone cannot be a cocompact lattice in
  `Aut(T_1) × Aut(T_2)` when both trees are infinite.
- If the projection closures are boundary-2-transitive, as for the Burger–Mozes lattices,
  every action of `Γ` on `S^1` has a global fixed point
  (`tree-product-lattice-circle-actions-have-fixed-points`).
- Hyde–Lodha, arXiv:2302.04805 (v3, HTML render), on the Burger–Mozes family: "For each
  of them it remains unknown whether it admits a nontrivial action by homeomorphisms on
  the real line."

## Attempts

- (z1-22-lo-simple-bm, 2026-09-13) **Expected answer: no, for the explicit Burger–Mozes
  lattices.** Their factors are boundary-2-transitive, their projections are dense, and they
  are perfect.
  - By the Deroin–Hurtado theorem, irreducible lattices in `p`-adic semisimple groups of rank
    at least two have no nontrivial action on the line
    (`higher-rank-p-adic-lattices-are-not-left-orderable`).
  - The analog for products of trees is `irreducible-tree-product-lattices-are-not-left-orderable`
    (open). It would refute this claim for every simple lattice whose projection closures are
    boundary-2-transitive, but not for simple lattices with other local actions.
  - The transcription of the p-adic proof (`research/artifacts/zp-tree-lattice-left-orderability-2026-09-13.md`)
    is settled except for Furstenberg's decomposition (Poisson boundary) and the technical points
    the exposition skips.
- (z1-22-lo-simple-bm, 2026-09-13) **Direct order.** An order would need compatible left
  orders on the free vertex groups of the graph of groups, respected by the finite-index
  edge inclusions. No candidate yet. The irreducibility of `Γ` makes the holonomy of the
  graph of groups non-periodic, which is where a compatible choice is expected to fail.
- (z1-22-lo-simple-bm, 2026-09-13) **Circle actions do not decide left orders.** Circle
  rigidity holds (`tree-product-lattice-circle-actions-have-fixed-points`). But a line action
  compactifies to a circle action with a fixed point at infinity, so that result is only an
  input to the Deroin–Hurtado argument, not a proof of non-orderability.
