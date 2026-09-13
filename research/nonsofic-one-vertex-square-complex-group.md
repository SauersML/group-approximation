---
rg: 2
id: nonsofic-one-vertex-square-complex-group
kind: claim
title: Some finite one-vertex VH square complex with complete bipartite links has a nonsofic fundamental group
distinct_from:
  strict-automaton-on-lattice-in-product-of-trees: that asks for an injective non-surjective automaton on some tree-product lattice, which is stronger than nonsoficity; this asks only for nonsoficity, and only for torsion-free vertex-transitive lattices
  radu-bmw-lattice-nonsofic: that is one lattice with torsion and four vertex orbits of its torsion-free subgroup; this asks for a torsion-free lattice acting simply transitively on vertices
---

**OPEN.** There is a finite one-vertex VH-T-complex `Z` whose fundamental group is not
sofic. Equivalently: some torsion-free cocompact lattice in `Aut(T_p) × Aut(T_q)` acts
simply transitively on the vertices of `T_p × T_q` and is not sofic. Then `p` and `q`
are even.

By Burger–Mozes Theorem 6.5 such `π_1(Z)` lies in a virtually simple lattice with dense
projections in `U(A_(2n)) × U(A_(2m))`
(`infinitely-transitive-nonsofic-lattice-from-one-vertex-complex`), and from there
`F_2 × F_2` gets a free mixing nonsofic action.

## Attempts

* **Necessary condition.** `π_1(Z)` must not be residually finite, since residually finite
  groups are sofic. Burger–Mozes record torsion-free non-residually-finite one-vertex
  complexes, for instance `A_(13,17) ⊠ A_(13,17)` (*Lattices in product of trees*,
  Proposition 2.4 and Corollary 2.5, cited in the proof of Theorem 6.4, p. 187).
* **Surjunctivity.** A strict automaton on `π_1(Z)` would make it nonsofic.
  `strict-automaton-on-lattice-in-product-of-trees` works on exactly these complete VH
  table hosts. No candidate automaton is known.
* **Kun--Thom mechanism.** Unavailable: these groups have the Haagerup property.
* **Soficity side.** `f2xf2-in-paunescu-class` would make all of them sofic.
