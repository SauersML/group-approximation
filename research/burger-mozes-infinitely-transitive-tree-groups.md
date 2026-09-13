---
rg: 2
id: burger-mozes-infinitely-transitive-tree-groups
kind: claim
title: Burger-Mozes structure of locally infinitely transitive tree groups, and embedding of every one-vertex square complex group in a virtually simple lattice with dense U(Alt) projections
distinct_from:
  howe-moore-property-for-simple-lie-and-p-adic-groups: that imports the Howe-Moore property; this imports the normal-subgroup structure of closed tree groups and the Burger-Mozes embedding theorem for square complexes
  radu-bmw-lattice-embeds-in-titz-witzel-kernel: that imports one explicit lattice with torsion and its embedding in a building lattice; this imports general structure theory and the embedding of torsion-free one-vertex complexes in Burger-Mozes lattices
---

**ESTABLISHED (literature import).** Let `T` be a locally finite tree and `H <= Aut(T)`
closed. `H^(∞)` is the intersection of all open finite-index subgroups of `H`.
`QZ(H)` is the set of elements with open centralizer.

1. **(Lemma 3.1.1.)** The following are equivalent: `H` is locally `∞`-transitive; `H`
   is non-compact and transitive on `∂T`; `H` is 2-transitive on `∂T`. They imply that
   every local action is 2-transitive and that `H` is non-discrete.
2. **(§1.1 and Proposition 1.2.1.)** Suppose `H` is non-discrete and locally
   quasiprimitive.
   * `H/H^(∞)` is compact.
   * `QZ(H)` acts freely on vertices, and is discrete and not cocompact.
   * Every closed normal subgroup `N` of `H` either is non-discrete, cocompact and
     contains `H^(∞)`, or is discrete and contained in `QZ(H)`.
   * Every normal cocompact subgroup contains `H^(∞)`.
3. **(Proposition 3.1.2.)** If `H` is locally `∞`-transitive, then `QZ(H) = e`, and
   `H^(∞)` is locally `∞`-transitive and topologically simple.
4. **(Universal groups.)** For `F <= S_d` 2-transitive, `U(F)^+ = U(F)^(∞)` has
   index 2 in `U(F)`, is simple, and is locally `∞`-transitive.
5. **(Proposition 5.2(2), Theorems 6.3–6.5.)** For every one-vertex VH-T-complex `Z`
   there is a one-vertex VH-T-complex `X` containing `Z` as a subcomplex with
   `π_1(Z) <= π_1(X)`, where `π_1(X)` is virtually simple. The complex `X` has
   horizontal and vertical permutation groups `A_(2n)` and `A_(2m)`, and
   `π_1(X) < U(A_(2n)) × U(A_(2m))` is an irreducible cocompact lattice with dense
   projections.

Sources: M. Burger, S. Mozes, *Groups acting on trees: from local to global structure*,
Publ. Math. IHÉS 92 (2000) 113–150 (items 1–3), and *Lattices in product of trees*,
same volume, 151–194 (items 4–5). Exact pages are in
`burger-mozes-infinitely-transitive-tree-groups-citation`.
