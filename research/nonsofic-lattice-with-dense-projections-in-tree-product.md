---
rg: 2
id: nonsofic-lattice-with-dense-projections-in-tree-product
kind: claim
title: Some lattice with dense projections in a product of two type-preserving tree automorphism groups is not sofic
distinct_from:
  radu-bmw-lattice-nonsofic: that is nonsoficity of one explicit lattice with no condition on its projections; this is existence of any nonsofic lattice whose projections are dense in the type-preserving automorphism groups
  f2xf2-admits-nonsofic-action: that asks for any free nonsofic action of F2 x F2; this asks for a nonsofic lattice in the envelope, which gives a mixing one
  nonsofic-hyperbolic-group: that asks for a nonsofic hyperbolic group; lattices in products of trees are never hyperbolic, since they contain Z^2
---

**OPEN.** For some `p, q >= 3` there is a lattice `Γ <= Aut(T_p)^+ × Aut(T_q)^+` whose
projections are dense in both factors and which is not a sofic group.

By `tree-product-lattice-nonsofic-gives-mixing-nonsofic-action`, such `Γ` gives the
residually finite group `K_p × K_q` (a product of free groups) an essentially free, mixing,
nonsofic p.m.p. action.

## Attempts

* **Radu's BMW lattice.** `Γ_R <= Aut(T_3) × Aut(T_3)` is irreducible and not residually
  finite. Its finite-index subgroup `Γ_R ∩ L^+` is a lattice of `L^+`, nonsofic iff `Γ_R`
  is. Two inputs are missing: `radu-bmw-lattice-nonsofic`, and density of the projections
  in `Aut(T_3)^+`. Irreducibility gives non-discrete projections only. Radu's algorithm for
  closures of projections (arXiv:1712.01091) assumes even degree at least `6` with
  alternating local action, so it does not cover `T_3`.
* **Kun--Thom mechanism.** Unavailable: `Aut(T_p) × Aut(T_q)` has the Haagerup property,
  and so do its lattices, so they contain no infinite Kazhdan subgroup.
* **A different envelope.** The transfer theorem also accepts closed boundary-2-transitive
  simple subgroups `G_i` in place of `Aut(T)^+`. The closures of the projections of an
  irreducible lattice are the natural choice, but then a sofic lattice of `G_1 × G_2` must
  be exhibited separately, since `K_p × K_q` need not lie there.
