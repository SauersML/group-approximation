---
rg: 2
id: radu-lattice-induced-actions-are-never-mixing
kind: claim
title: No action induced from Radu's BMW lattice through a product envelope is mixing for a cocompact lattice, since its vertical closure is locally intransitive and its horizontal kernel is infinite
distinct_from:
  induced-lattice-action-mixing-forces-c0-homogeneous-space: that is the general necessary condition for mixing of induced actions; this verifies that Radu's lattice fails it for every product envelope
  radu-horizontal-projection-kills-delta-squared: that computes the kernel of the horizontal tree action; this uses that kernel and the vertical local action to exclude every induced mixing action
  tree-product-lattice-nonsofic-gives-mixing-nonsofic-action: that is the positive mixing transfer for lattices with dense projections in simple tree groups; this shows Radu's lattice can never be its seed
---

**ESTABLISHED.** Let `Γ_R <= Aut(T_h) × Aut(T_v)` be Radu's BMW lattice
(`radu-bmw-lattice-embeds-in-titz-witzel-kernel`), with `A = <a,b,c>` the stabilizer
of the root `o` of `T_v = Γ_R/A`, `V = <x,y,z>` the stabilizer of the root of
`T_h = Γ_R/V`, and `H_h`, `H_v` the closures of the two projections.

1. **Vertical local action.** At every vertex of `T_v` the local action of `H_v` is
   the group `<(xA zA)> ≅ C_2`, which fixes the `y`-edge. So `H_v` is not locally
   transitive, and no finite-index subgroup of `Γ_R` has projection dense in
   `Aut(T_3)^+` or in any locally transitive closed subgroup of `Aut(T_v)`.
2. **Horizontal kernel.** `Λ_v = ker(Γ_R → Aut(T_h))` contains `(xz)^2`, which has
   infinite order. `Λ_v` lies in `{1} × H_v` and is a normal subgroup of
   `H_h × H_v`.
3. **No induced mixing.** Let `L = G_1 × G_2` with `G_1 <= Aut(T_h)` and
   `G_2 <= Aut(T_v)` closed and `Γ_R <= L`. For every p.m.p. `Γ_R`-space `Z` and
   every cocompact lattice `Λ <= L`, the action `Λ ↷ L ×_(Γ_R) Z` is not mixing.
   * If `G_2 ≠ H_v`, the closed non-compact subgroup `G_1` has nonconstant
     invariant functions on `L/Γ_R`, pulled back from `G_2/H_v`.
   * If `G_2 = H_v`, the infinite subgroup `Λ_v <= Γ_R` is normal in `L`.

   Both violate `induced-lattice-action-mixing-forces-c0-homogeneous-space`.

**Consequences.**
* Density of the projections of `Γ_R ∩ (Aut(T_3)^+ × Aut(T_3)^+)`, one of the two inputs
  listed for Radu's lattice in `nonsofic-lattice-with-dense-projections-in-tree-product`,
  is false. So is density in any locally transitive envelope.
* Even if `radu-bmw-lattice-nonsofic` holds, the induced-action transfer
  (`tree-product-lattice-nonsofic-gives-mixing-nonsofic-action`) produces no mixing
  action from `Γ_R` over any product envelope. The non-mixing transfer
  `f2xf2-nonsofic-action-from-radu-lattice-nonsofic` is unaffected.
* A mixing witness from Radu's lattice would need a lattice with locally
  `∞`-transitive projections that contains `Γ_R`, or a coupling not induced from a
  common envelope.

Proof in `radu-lattice-induced-actions-are-never-mixing-proof`.
