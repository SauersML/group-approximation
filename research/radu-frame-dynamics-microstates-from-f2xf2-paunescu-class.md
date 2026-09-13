---
rg: 2
id: radu-frame-dynamics-microstates-from-f2xf2-paunescu-class
kind: route
title: If every p.m.p. action of F2 x F2 is sofic, the second-place frame dynamics of Radu's arithmetic quotient is sofic and admits microstates
target: radu-second-prime-frame-dynamics-admit-microstates
requires:
  - f2xf2-in-paunescu-class
  - product-tree-lattices-in-paunescu-class-iff-f2xf2
  - uniquely-ergodic-action-sofic-iff-topological-microstates
  - radu-horizontal-quotient-is-arithmetic-lattice
---

Conditional route. It fires when `f2xf2-in-paunescu-class` is established.

1. **`Q` is a tree-product lattice.** `Q` acts properly and cocompactly on `T_h × T'`, a product of
   two 3-regular trees, with finite vertex stabilizers `S_3`
   (`radu-horizontal-quotient-is-arithmetic-lattice`). Its image in `Aut(T_h) × Aut(T')` is therefore
   a cocompact lattice. The kernel of the action is a finite normal subgroup. It is trivial because
   `ρ` is faithful on the second tree, where `PGL_2(F_(𝔮'))` acts faithfully.
2. **Every p.m.p. action is sofic.** By `product-tree-lattices-in-paunescu-class-iff-f2xf2` and
   `f2xf2-in-paunescu-class`, every p.m.p. action of `Q` is sofic, in particular `Q ↷ (L/Λ, Haar)`.
3. **Microstates.** `Q` is residually finite, hence sofic, and it acts on the compact metric space
   `L/Λ` by homeomorphisms preserving Haar measure. Item 1 of
   `uniquely-ergodic-action-sofic-iff-topological-microstates` then gives `(F,ε)`-microstates for all
   `F` and `ε`.

∎
