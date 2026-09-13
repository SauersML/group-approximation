---
rg: 2
id: nonsofic-infinitely-transitive-tree-lattice
kind: claim
title: Some cocompact tree-product lattice with locally infinitely transitive projection closures of finite H^(infinity) index is not sofic
distinct_from:
  nonsofic-lattice-with-dense-projections-in-tree-product: that asks for projections dense in Aut(T)^+, for a lattice that need not be cocompact; this asks for cocompact lattices with any locally infinitely transitive closures, such as U(Alt(d)), which carry the Burger-Mozes simple lattices and every one-vertex square complex group
  radu-bmw-lattice-nonsofic: that is one explicit lattice whose vertical closure is locally intransitive, so it is not an instance of this claim
  nonsofic-one-vertex-square-complex-group: that asks for a nonsofic torsion-free vertex-transitive lattice with no condition on projections, which implies this claim by the Burger-Mozes embedding
---

**OPEN.** For some `p, q >= 3` there is a cocompact lattice
`Γ <= Aut(T_p) × Aut(T_q)` with the following property. For `i = 1, 2`, the closure
`H_i` of the `i`-th projection is locally `∞`-transitive and `H_i^(∞)` has finite
index in `H_i`. And `Γ` is not sofic.

By `nonsofic-infinitely-transitive-tree-lattice-gives-mixing` such `Γ` gives `F_2 × F_2` a
free mixing nonsofic action.

**What a witness would be.** Suppose `Γ = π_1(X)` for a finite VH-T-complex `X` whose
permutation groups are alternating of degree at least 6. If `Γ` is not residually
finite, Burger–Mozes Corollary 5.4 (*Lattices in product of trees*, p. 179) makes its
finite residual a finite-index simple subgroup. A witness of that kind is a finitely
presented, torsion-free, simple nonsofic group with the Haagerup property. The unit
groups recorded in `fp-simple-nonsofic-group` are all Kazhdan-type.

## Attempts

* **Reduction to one-vertex complexes (live).**
  `infinitely-transitive-nonsofic-lattice-from-one-vertex-complex`: by Burger–Mozes
  Theorem 6.5 (`burger-mozes-infinitely-transitive-tree-groups`, item 5), a nonsofic
  one-vertex square complex group embeds in a lattice with dense projections in
  `U(A_(2n)) × U(A_(2m))`.
* **Radu's BMW lattice (conditional on an embedding).**
  `infinitely-transitive-nonsofic-lattice-from-radu-lattice` needs `radu-bmw-lattice-nonsofic`
  and `radu-bmw-lattice-embeds-in-infinitely-transitive-tree-lattice`.
* **Kun--Thom mechanism.** Unavailable: these lattices have the Haagerup property.
* **Soficity side.** `f2xf2-in-paunescu-class` would make every cocompact tree-product
  lattice sofic (`product-tree-lattices-in-paunescu-class-iff-f2xf2`), refuting this claim.
