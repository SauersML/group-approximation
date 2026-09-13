---
rg: 2
id: radu-bmw-lattice-sofic-from-f2xf2-paunescu-class
kind: route
title: If every action of F2 x F2 is sofic, then every action of Radu's lattice is sofic, so the lattice is sofic
target: radu-bmw-lattice-sofic
requires:
  - f2xf2-in-paunescu-class
  - product-tree-lattices-in-paunescu-class-iff-f2xf2
  - radu-bmw-lattice-embeds-in-titz-witzel-kernel
---

Conditional route; it fires when `f2xf2-in-paunescu-class` is established.

1. `Gamma_R` acts simply transitively on the vertices of a product of two
   3-regular trees (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`), so it is a
   cocompact lattice in `Aut(T_3) × Aut(T_3)`.
2. By `product-tree-lattices-in-paunescu-class-iff-f2xf2` and
   `f2xf2-in-paunescu-class`, every p.m.p. action of `Gamma_R` is sofic.
3. Take the Bernoulli shift of `Gamma_R`. A sofic embedding of its crossed product
   sends the `u_g` to permutations with vanishing trace for `g ≠ 1`, i.e. a sofic
   representation of `Gamma_R`. So `Gamma_R` is sofic.

This is harder than `radu-bmw-lattice-sofic` itself would need, since it asks for
soficity of all actions of `F_2 × F_2`; its value is that the target becomes a
statement about one residually finite group.
