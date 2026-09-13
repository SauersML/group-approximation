---
rg: 2
id: tree-product-lattice-circle-actions-have-fixed-points-proof
kind: route
title: Burger's extension criterion for products kills minimal circle actions because tree groups have no nontrivial continuous circle images
target: tree-product-lattice-circle-actions-have-fixed-points
requires: []
artifacts:
  - research/artifacts/zp-tree-lattice-left-orderability-2026-09-13.md
---

**Imports.** From M. Burger, *An extension criterion for lattice actions on the circle*,
arXiv:0905.0136v1 (1 May 2009), read from the PDF on 2026-09-13.

- p. 9, trichotomy (3.6), for `ρ : Γ → Homeo_+(S^1)`: "1) There is a finite orbit and all finite
  orbits have the same cardinality. 2) The action is minimal. 3) There is a unique proper minimal
  invariant closed subset `F ⊊ S^1`, which is a Cantor set." In case 2, `ρ(Γ)` "is either bounded
  (equicontinuous), preserves hence a probability measure μ necessarily with full support and no
  atoms, and can be conjugated into the subgroup of rotations ...; or ρ(Γ) is unbounded". In case 3,
  collapsing the components of `S^1 ∖ F` gives "a continuous quasi-conjugacy between ρ and a minimal
  action".
- p. 4, **Corollary 1.9**: "Let `G = G_1 × ⋯ × G_n` be a product of locally compact second countable
  groups and `Γ < G` a lattice with dense projections on each factor `G_i`. Assume that
  `ρ : Γ → Homeo^+(S^1)` is minimal unbounded. Then the strongly proximal quotient `ρ_sp` extends
  continuously to `G`, `(ρ_sp)^ext : G → Homeo^+(S^1)` and we have one of the following, 1)
  `Ker(ρ_sp)^ext` is open in `G`. 2) Up to conjugation `(ρ_sp)^ext` factors via a projection onto some
  factor `G_i` followed by a continuous surjection onto `PSL(2,R) ⊂ Homeo^+(S^1)`."

From `burger-mozes-infinitely-transitive-tree-groups` (established import): each `G_i` is locally
`∞`-transitive, so its local actions are 2-transitive, hence quasiprimitive, and `G_i` is non-discrete
(item 1). `QZ(G_i) = e` (item 3). Every closed normal subgroup of `G_i` is either discrete and
contained in `QZ(G_i)`, or cocompact (item 2).

**Proof.** `G_i` is a closed subgroup of the automorphism group of a locally finite tree, so it is
locally compact, second countable and totally disconnected.

1. **No continuous surjection `G_i → PSL(2,R)`.** Let `φ : G_i → PSL(2,R)` be continuous and let `V` be
   a compact open subgroup of `G_i`. `φ(V) ≅ V/(V ∩ ker φ)` is a profinite group and a compact
   subgroup of a Lie group, hence a profinite Lie group, hence finite. So `V ∩ ker φ` is open, so
   `ker φ` is open. By second countability `G_i/ker φ` is countable, so `φ` is not onto.
2. **An open normal subgroup of `G` has finite index.** Let `N ⊴ G` be open. `N_1 = N ∩ (G_1 × 1)` is
   an open normal subgroup of `G_1`. It is nontrivial because `G_1` is non-discrete, so it is not
   discrete, so it is cocompact. It is also open, so `G_1/N_1` is compact and discrete, hence finite.
   Likewise for `N_2`. So `G/N` is a quotient of the finite group `G/(N_1 × N_2)`.
3. **Minimal unbounded actions do not exist.** Suppose `ρ'` is a minimal unbounded action of `Γ`. By
   Corollary 1.9, `(ρ_sp)^ext` exists. Alternative 2) is excluded by step 1. So `Ker(ρ_sp)^ext` is open,
   and by step 2 `(ρ_sp)^ext(G)` is finite. Then `ρ_sp(Γ)` is a finite group of circle homeomorphisms,
   whose orbits are finite, so `ρ_sp` is not minimal. But `ρ_sp` is a topological circle factor of the
   minimal action `ρ'`, hence minimal. Contradiction.
4. **Minimal bounded actions do not exist.** Such an action is conjugate into the rotation group, so
   `ρ(Γ)` is abelian, hence trivial because `Γ` is perfect. The trivial action is not minimal.
5. **Cantor case.** In case 3 of the trichotomy, `ρ` is continuously quasi-conjugate to a minimal
   action `ρ'` of `Γ`. By steps 3 and 4 there is none. So case 3 does not occur.
6. **Finite orbits are fixed points.** So case 1 holds. `Γ` permutes a finite orbit `O` by
   orientation-preserving homeomorphisms, which induce cyclic rotations of the cyclically ordered set
   `O`. So `Γ` acts on `O` through a cyclic group, and since `Γ` is perfect it acts trivially. Every
   point of `O` is a global fixed point.
