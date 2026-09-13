---
rg: 2
id: nonsofic-infinitely-transitive-tree-lattice-gives-mixing
kind: claim
title: A nonsofic tree-product lattice with locally infinitely transitive projection closures gives F2 x F2 a free mixing nonsofic action
distinct_from:
  tree-product-lattice-nonsofic-gives-mixing-nonsofic-action: that needs dense projections in two simple boundary-2-transitive groups and a lattice of that product; this starts from the closures of the projections of any cocompact lattice, extracts the simple groups and a product-of-free-groups lattice there, and lands on F2 x F2
  radu-lattice-induced-actions-are-never-mixing: that shows Radu's BMW lattice, whose vertical closure is locally intransitive, can never seed an induced mixing action; this is the positive theorem for lattices whose closures are locally infinitely transitive
  f2xf2-admits-nonsofic-action: that asks for any free nonsofic action of F2 x F2, which any nonsofic tree-product lattice supplies without mixing; this produces a mixing one under a hypothesis on the projections
---

**ESTABLISHED (unreviewed).** Let `p, q >= 3` and let `Γ <= Aut(T_p) × Aut(T_q)` be a
cocompact lattice, with closures `H_1`, `H_2` of its projections. Assume, for `i = 1, 2`:

* `H_i` is locally `∞`-transitive (equivalently, 2-transitive on `∂T`);
* `H_i^(∞)` has finite index in `H_i`.

If `Γ` is not sofic, then:

1. `G_i := H_i^(∞)` is closed, open, topologically simple and 2-transitive on `∂T`.
   `Γ' := Γ ∩ (G_1 × G_2)` is a nonsofic cocompact lattice of `G_1 × G_2` of finite
   index in `Γ`, with dense projections.
2. `G_1 × G_2` contains a cocompact lattice `F_m × F_n` with `m, n >= 2`.
3. `F_m × F_n` acts on `W = (G_1 × G_2) ×_(Γ') ({0,1},fair)^(Γ')` essentially freely,
   mixingly and not soficly.
4. The co-induced action of `F_2 × F_2` from its finite-index subgroup `F_m × F_n` is
   essentially free, mixing and not sofic. `F_2 × F_2` is residually finite, so this
   answers `mixing-free-nonsofic-action-of-sofic-group`.

**Who satisfies the hypothesis.**
* Lattices with dense projections in `U(F_1) × U(F_2)` for 2-transitive `F_i`, where
  `U(F)^(∞) = U(F)^+` has index 2 (`burger-mozes-infinitely-transitive-tree-groups`,
  item 4). This covers the Burger–Mozes virtually simple lattices, and every one-vertex
  square complex group after the embedding of item 5 there.
* Lattices with dense projections in `Aut(T_p)^+ × Aut(T_q)^+`.

**Who fails it.** Reducible lattices have discrete closures. Radu's BMW lattice has a
locally intransitive vertical closure (`radu-lattice-induced-actions-are-never-mixing`).

Proof in `nonsofic-infinitely-transitive-tree-lattice-gives-mixing-proof`.
