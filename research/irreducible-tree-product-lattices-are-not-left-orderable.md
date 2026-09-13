---
rg: 2
id: irreducible-tree-product-lattices-are-not-left-orderable
kind: claim
title: Cocompact lattices with dense projections in products of two boundary-2-transitive tree groups are not left-orderable
distinct_from:
  higher-rank-p-adic-lattices-are-not-left-orderable: that imports the Deroin–Hurtado theorem for lattices in algebraic p-adic groups; this asks for the same conclusion for lattices in products of non-algebraic tree groups, including non-linear simple lattices
---

**OPEN.** Let `T_1`, `T_2` be locally finite trees and let `G_i ≤ Aut(T_i)` be closed,
non-compact and 2-transitive on `∂T_i`. Let `Γ ≤ G_1 × G_2` be a cocompact lattice whose
projections to `G_1` and to `G_2` are dense. Then `Γ` has no faithful action on `R` by
orientation-preserving homeomorphisms, i.e. `Γ` is not left-orderable. For simple `Γ` this
says every action of `Γ` on `R` is trivial.

**Consequence.** It refutes `some-simple-lattice-in-a-product-of-trees-is-left-orderable`
for every simple lattice whose projection closures are boundary-2-transitive. That includes
the Burger–Mozes simple lattices in `U(A_(2n)) × U(A_(2m))`: projections dense and
`U(F)^+` locally `∞`-transitive for 2-transitive `F`
(`burger-mozes-infinitely-transitive-tree-groups`, items 1, 4, 5). A finite-index subgroup
has projection closures of finite index, and these contain `U(F)^+`, so the hypotheses
pass to the simple subgroup.

**Calibration.**

- Dense projections are needed. `F_2 × F_2` is a reducible cocompact lattice in
  `Aut(T_4) × Aut(T_4)` and is bi-orderable.
- The arithmetic case is known: torsion-free irreducible lattices in
  `SL(2,Q_p) × SL(2,Q_p)` are not left-orderable
  (`higher-rank-p-adic-lattices-are-not-left-orderable`).
- A left-orderable simple lattice would answer Zaremsky Problem 1.22 affirmatively, so this
  claim is also where that route dies.

## Attempts

- (z1-22-lo-simple-bm, 2026-09-13) **Transcribe the Deroin–Hurtado proof, following Witte
  Morris §3.** The steps and their tree-group inputs:
  - almost-periodic space `Z` and induced `X = Ind_Γ^G Z` (Theorem 3.15, Definition 3.17):
    general for finitely generated groups;
  - stationary `μ_X` (Corollary 3.27) and Furstenberg's decomposition over a minimal
    parabolic `P` (Theorem 3.28). Use `P = G_(1,ξ_1) × G_(2,ξ_2)`, a product of end
    stabilizers, which is amenable with `G = KP` for `K` a vertex stabilizer. This needs the
    Poisson boundary of a bi-`K`-invariant spread-out `μ_G` to be `∂T_1 × ∂T_2`;
  - Proposition 3.29, that `μ_X` is not `G`-invariant: uses only that a faithful action by
    translations forces `Γ` abelian;
  - `χ_P : A → R` on `A = ⟨(a_1,1),(1,a_2)⟩ ≅ Z^2` for hyperbolic `a_i` fixing `ξ_i`,
    local and global contraction (Lemma 3.32, Key Proposition 3.33). Karlsson–Margulis
    tracking holds in the CAT(0) space `T_1 × T_2`, but it needs a drift direction realized
    by one element `â_P ∈ A`, since `A` is discrete;
  - invariance under centralizers (Corollary 3.35), which needs a full-support statement
    for `ᶜP`-invariant probability measures on `G/Γ` (Proposition 2.8(2)) and an open big
    cell `P_a^- U_a^+`. The big cell is plausible for groups with Tits' independence
    property, such as `U(F)`;
  - propagation (Corollary 3.42). For products the centralizer of a wall element
    `(a_1, 1)` contains `1 × G_2`, so one negative wall value already gives a whole factor.
- **Where it can die.**
  - (G1) The exposition assumes `G = KΓ`. One-vertex square complex lattices satisfy it,
    but their simple finite-index subgroups do not, so the harmonic-function version
    (Witte Morris §5) is needed unless some simple torsion-free lattice acts simply
    transitively on vertices.
  - (G6) The Figure 1 propagation argument for `SL(3,Q_p)` uses 60-degree chambers. For a
    product of two rank-one groups the chambers are quadrants, and the case where `χ_P`
    vanishes on exactly one wall of `W_P` is not covered by that picture. Remark 3.4(2)
    says `SL(2,Q_p) × SL(2,Q_p)` is covered, so the general Corollary 4.17 treatment must
    be read and transcribed.
  - Also to check: Proposition 2.8(2), the open big cell, and the Poisson boundary
    identification for non-algebraic `G_i`.
