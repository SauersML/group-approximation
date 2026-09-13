---
rg: 2
id: f2xf2-nonsofic-action-from-radu-lattice-nonsofic
kind: route
title: A nonsofic Radu lattice transfers a free nonsofic action to F2 x F2 through the product of two trees
target: f2xf2-admits-nonsofic-action
requires:
  - radu-bmw-lattice-nonsofic
  - product-tree-lattices-in-paunescu-class-iff-f2xf2
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
---

Conditional route; it fires when `radu-bmw-lattice-nonsofic` is established.

1. A nonsofic group has no sofic p.m.p. action, so `Gamma_R ∉ 𝒮`.
2. `Gamma_R` is a cocompact lattice in `Aut(T_3) × Aut(T_3)`
   (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`). By
   `product-tree-lattices-in-paunescu-class-iff-f2xf2`, `F_2 × F_2 ∉ 𝒮`.
3. By Păunescu Theorem 3.1 (`paunescu-sofic-action-class-permanence`), a group
   outside `𝒮` has a free nonsofic action: multiply a nonsofic action by the
   Bernoulli shift and use that factors of sofic actions are sofic.

Explicitly, with `C_2^(*3) × C_2^(*3)` coupled to `Gamma_R` by Haar measure on
`L = Aut(T_3) × Aut(T_3)` and `B` the Bernoulli shift of the product of the two
lattices, `C_2^(*3) × C_2^(*3)` acts freely and nonsoficly on `(L × B)/Gamma_R`,
and the restriction of that action to the finite-index subgroup `K_3 × K_3`
(a product of free groups, commensurable with `F_2 × F_2`) is still nonsofic: by
the monomial induction of `sofic-action-class-commensurability-proof` (Part 2), a
sofic restriction to a finite-index subgroup makes the whole action sofic.
