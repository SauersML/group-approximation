---
rg: 2
id: irreducible-tree-product-lattices-are-not-left-orderable
kind: claim
title: Cocompact lattices with dense projections in products of two boundary-2-transitive tree groups are not left-orderable
distinct_from:
  higher-rank-p-adic-lattices-are-not-left-orderable: that imports the Deroin–Hurtado theorem for lattices in algebraic p-adic groups; this asks for the same conclusion for lattices in products of non-algebraic tree groups, including non-linear simple lattices
artifacts:
  - research/artifacts/zp-tree-lattice-left-orderability-2026-09-13.md
---

**OPEN.** Let `T_1`, `T_2` be locally finite trees and let `G_i ≤ Aut(T_i)` be closed,
non-compact and 2-transitive on `∂T_i`. Let `Γ ≤ G_1 × G_2` be a cocompact lattice whose
projections to `G_1` and to `G_2` are dense. Then `Γ` has no faithful action on `R` by
orientation-preserving homeomorphisms, i.e. `Γ` is not left-orderable. For simple `Γ` this
says every action of `Γ` on `R` is trivial.

**Consequence.** It refutes `some-simple-lattice-in-a-product-of-trees-is-left-orderable`
for every simple lattice whose projection closures are boundary-2-transitive. That includes the
Burger–Mozes simple lattices in `U(A_(2n)) × U(A_(2m))`: projections dense and `U(F)^+` locally
`∞`-transitive for 2-transitive `F` (`burger-mozes-infinitely-transitive-tree-groups`, items 1,
4, 5). A simple subgroup of finite index lies in `U(F_1)^+ × U(F_2)^+`, since it has no proper
finite-index subgroup, and it projects densely there.

**Calibration.**

- Dense projections are needed. `F_2 × F_2` is a reducible cocompact lattice in
  `Aut(T_4) × Aut(T_4)` and is bi-orderable.
- The arithmetic case is known: torsion-free irreducible lattices in
  `SL(2,Q_p) × SL(2,Q_p)` are not left-orderable
  (`higher-rank-p-adic-lattices-are-not-left-orderable`).
- A left-orderable simple lattice would answer Zaremsky Problem 1.22 affirmatively, so this
  claim is also where that route dies.

## Attempts

- (z1-22-lo-simple-bm, 2026-09-13) **Transcribe Deroin–Hurtado as exposed by Witte Morris**
  (arXiv:2407.09742v1). The artifact records the dictionary, a step table and the status of each
  step. For perfect `Γ` with `G_i = U(F_i)^+`, `F_i` 2-transitive:
  - **Settled.** Almost-periodic space, induced space and stationarity: general, with `G ≠ KΓ`
    handled by the harmonic extension of Witte Morris §5, which uses only `K` open and `Γ`
    cocompact. Non-invariance of `μ_X`, since `Γ` is perfect. `χ_P` and local contraction. The
    Case 1 propagation, because the four products of end stabilizers generate `G`. The Case 2
    propagation, written out for trees in artifact §4, where the forced abelian subgroup
    `Γ ∩ (K_1 × G_2)` is a non-abelian free vertex stabilizer.
  - **Settled.** Circle rigidity, used in Theorem 4.1(2) and Proposition 4.19
    (`tree-product-lattice-circle-actions-have-fixed-points`).
  - **Available by import.** Howe–Moore for topologically simple boundary-2-transitive tree
    groups (`howe-moore-property-for-simple-lie-and-p-adic-groups`, item 3). Together with dense
    projections this gives Moore ergodicity of hyperbolic wall elements on `G/Γ`.
  - **Sketched.** Open big cell `P_a^- U_a^+` for groups with Tits' independence property and
    2-transitive local actions (artifact §3, step 9). Drift direction realized in the discrete
    `A ≅ Z^2` by tuning a product of isotropic random walks (artifact part 2).
- **Open inputs.**
  - (G4) Furstenberg's decomposition `μ_X = ∫_K k_* μ_X^P dm_K` with a unique `P`-invariant
    `μ_X^P`. This is the Poisson boundary of `μ_G = μ_1 ⊗ μ_2` being `∂T_1 × ∂T_2`.
  - The measure-theoretic points the exposition declares ignored: ergodic components in
    Corollary 3.35 and Lemma 4.14, and `μ_X` versus `μ_X^P` in Remark 4.21.
