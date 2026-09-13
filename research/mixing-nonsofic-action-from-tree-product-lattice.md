---
rg: 2
id: mixing-nonsofic-action-from-tree-product-lattice
kind: route
title: A nonsofic lattice with dense projections in a product of trees gives a product of free groups a free mixing nonsofic action
target: mixing-free-nonsofic-action-of-sofic-group
requires:
  - nonsofic-lattice-with-dense-projections-in-tree-product
  - tree-product-lattice-nonsofic-gives-mixing-nonsofic-action
---

Conditional route; it fires when `nonsofic-lattice-with-dense-projections-in-tree-product`
is established.

1. Let `Γ <= L^+ = Aut(T_p)^+ × Aut(T_q)^+` be the nonsofic lattice with dense projections.
2. `K_p × K_q` is a lattice of `L^+` and a product of free groups, so it is residually finite
   and sofic.
3. `tree-product-lattice-nonsofic-gives-mixing-nonsofic-action` with `Λ = K_p × K_q` gives
   the essentially free, mixing, nonsofic action `K_p × K_q ↷ L^+ ×_Γ ({0,1},fair)^Γ`.

This is a second conditional source for the mixing root, independent of the Howe--Moore
lattices of `mixing-nonsofic-action-from-simple-lattice-nonsofic-action`. Its seed lives in
the Haagerup world of lattices in products of trees, where the Kun--Thom mechanism is
absent, so it needs the second nonsoficity mechanism, for instance the surjunctivity or
commutator-collapse routes into `radu-bmw-lattice-nonsofic`.
