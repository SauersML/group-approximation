---
rg: 2
id: ascending-hnn-quotients-affiliated-h1-proof
kind: route
title: Lück's mapping-torus theorem in degree 2 makes the d mapping-torus relators span all 1-cycles over U(G), and regularity turns dimension into equality
target: ascending-hnn-quotients-have-vanishing-affiliated-first-homology
requires:
  - lueck-mapping-tori-and-homology-invariance
  - lueck-dimension-additivity-cofinality-and-induction
---

Notation: `NG` is the group von Neumann algebra, `U = U(G)` the algebra of affiliated operators,
and `Z[G] ⊆ NG ⊆ U`. Modules are left modules, and `U` is a right `Z[G]`-module.

## Imports about `U`

These are the same imports as (J1) and (J2) in `amenable-fp-iff-affiliated-top-homology-vanishes-proof`
(W. Lück, *L²-invariants*, Springer 2002, Chapter 8; K. R. Goodearl, *Von Neumann regular rings*,
Theorem 1.11). They are recalled, and the section numbers have not been re-checked.

- **(J1)** `U` is the Ore localization of `NG`, so it is flat over `NG`. There is a dimension
  `dim_U` on all `U`-modules with `dim_U(U ⊗_NG M) = dim_NG M`. It is additive on short exact
  sequences, and a finitely generated projective `U`-module of dimension 0 is zero.
- **(J2)** `U` is von Neumann regular. So a finitely generated submodule of a projective module is
  a direct summand, and a finitely presented module is projective.

No amenability is used anywhere.

## Proof of item 1

Let `K = ⟨h_1, …, h_d⟩`, and let `t` and `χ` be as in the statement.

**Step 1 (the mapping torus).** This is Steps 1–3 of `ascending-hnn-one-cell-l2-vanishing-proof`
verbatim, with `σ(h) = t h t⁻¹`.

- Let `X` be the rose with one 0-cell `v` and 1-cells `x_1, …, x_d`.
- Choose words `w_j` with `w_j(h) = t h_j t⁻¹ ∈ K`.
- Let `f : X → X` send the `j`-th circle along `w_j`.

`T_f` has one 0-cell, the 1-cells `x_j` and `τ`, and `d` 2-cells with attaching words
`x_j τ w_j⁻¹ τ⁻¹`. Define `φ : π₁(T_f) → G` by `x_j ↦ h_j` and `τ ↦ t⁻¹`.

- `φ` is well defined, because `φ(τ⁻¹ x_j τ) = t h_j t⁻¹ = φ(w_j)`.
- `φ` is onto, because `G = ⟨K, t⟩`.
- `ψ = −χ` satisfies `ψ ∘ φ = p_*`, the canonical epimorphism (`x_j ↦ 0`, `τ ↦ 1`), and `ψ` is onto.

That proof used the isomorphism `G ≅ H *_σ` only to produce `χ`. Here `χ` is given, so no
isomorphism is needed.

**Step 2 (Lück in degree 2).** `Y = G ×_{φ∘i} X̃` has cellular chain complex `ZG^d → ZG`. So
`b_2^(2)(Y) = 0` and `b_1^(2)(Y) ≤ d`, both finite. This uses
`lueck-mapping-tori-and-homology-invariance` item 1 and additivity from
`lueck-dimension-additivity-cofinality-and-induction`, exactly as in Step 3 of the one-cell proof.
Item 3 of `lueck-mapping-tori-and-homology-invariance` with `p = 2` gives
`b_2^(2)(T̄_f; N(G)) = 0`, where `T̄_f` is the covering of `T_f` associated to `φ`.

**Step 3 (`∂_2` is injective over `U`).** The cellular complex of `T̄_f` is

  `C_2 = ZG^d --∂_2--> C_1 = ZG^{d+1} --∂_1--> C_0 = ZG`.

Put `D_• = U ⊗_{ZG} C_•`. Then `D_• = U ⊗_NG (NG ⊗_ZG C_•)`. By flatness (J1),
`dim_U H_2(D_•) = b_2^(2)(T̄_f) = 0`. Also `H_2(D_•) = ker(∂_2^U)`. The image of `∂_2^U` is a
finitely generated submodule of `U^{d+1}`, so it is projective (J2). So `ker ∂_2^U` is a direct
summand of `U^d`, and it is finitely generated projective of dimension 0. By (J1) it is zero.
Hence `∂_2^U` is injective, and `B := im ∂_2^U ≅ U^d` has dimension `d`.

**Step 4 (cycles).** `H_0(D_•) = U ⊗_ZG Z` is finitely presented (it is `coker ∂_1^U`), hence
projective (J2). Its dimension is `b_0^(2)(T̄_f) = b_0^(2)(G)`. That is 0, because `G` is infinite
(`χ` is onto `Z`), by Lück, *op. cit.*, Theorem 6.54(8), which is also recalled as (J3) in the
amenable-fp proof. So `H_0(D_•) = 0` by (J1). Then `∂_1^U : U^{d+1} → U` is onto and splits, and
`Z := ker ∂_1^U` is a finitely generated projective direct summand of dimension `d`.

**Step 5 (boundaries fill the cycles).** `B ⊆ Z`, and `B` is finitely generated, so by (J2) `B`
is a direct summand of `Z`, say `Z = B ⊕ C`. Then `C` is a finitely generated projective module
with `dim C = d − d = 0`, so `C = 0` by (J1). Thus `B = Z`, that is, `H_1(D_•) = 0`.

**Step 6 (from `T_f` to `G`).** Complete the relators `x_j τ w_j⁻¹ τ⁻¹` to a presentation of `G`
on the generators `x_1, …, x_d, τ`. Its presentation complex `P` has the same 1-skeleton as `T_f`,
the `d` 2-cells of `T_f`, and possibly infinitely many further 2-cells. So `T_f ⊆ P`, and the
restriction of the universal cover `P̃ → P` to `T_f` is the covering `T̄_f`, because
`π₁(T_f) → π₁(P) = G` is `φ`.

`P̃` is simply connected, so `C_2(P̃) → C_1(P̃) → C_0(P̃) → Z → 0` is exact. This is the beginning
of a free resolution of `Z`, and so

  `H_1(G; U) = ker(∂_1^U) / im(∂_2^{P,U})`.

The degree-1 and degree-0 terms coincide with those of `T̄_f`, and `im ∂_2^{P,U} ⊇ im ∂_2^U = Z`.
Hence `H_1(G; U) = 0`. ∎

## Proof of item 2

Let `G` be finitely generated with `Σ¹(G) ≠ ∅`. Two facts are recalled here without re-checked
pinpoints.

- `Σ¹(G)` is open in the character sphere `S(G)` (R. Bieri, W. Neumann, R. Strebel, Invent. Math.
  90 (1987), Theorem A).
- Rational points, that is, discrete characters `χ : G ↠ Z` up to positive scaling, are dense in
  `S(G)`.

So `Σ¹(G)` contains a discrete character `χ`. By BNS 1987, §4 (see also K. S. Brown, Invent. Math.
90 (1987), and R. Strebel, *Notes on the Sigma invariants*, arXiv:1204.0214), a discrete character
lies in `Σ¹(G)` exactly when `G` is an ascending HNN extension with finitely generated base
`K ≤ ker χ` and stable letter `t` with `χ(t) = ±1`, the sign depending on the convention.
Replacing `(t, χ)` by `(t⁻¹, −χ)` if necessary gives `t K t⁻¹ ⊆ K`, `χ(K) = 0` and `χ(t) = 1`.
Item 1 applies. ∎

## Checks

- **Where degree 2 enters.** The one-cell proof used Lück's theorem only for `p = 1`, which gives
  `dim H_1 = 0`. For a non-`FP_2` group this is strictly weaker than `H_1 = 0`: in an amenable
  counterexample to Kropholler's question, `dim H_1 = 0` but `H_1 ≠ 0`. Here `p = 2` is used on
  the finite complex `T_f`, whose relation module has full rank `d`. Exactness then follows from
  finiteness on `T_f` alone, whatever the rest of the presentation is.
- **Cone check.** For `G = K × Z` with `K` finitely generated, `U ⊗_ZG C(EG)` is the mapping cone
  of right multiplication by `t − 1` on `U ⊗_{ZK} C(EK)`. Since `t − 1` is a non-zero-divisor of
  `N⟨t⟩ ⊆ NG`, it is a unit in `U`, so the cone is acyclic. This matches item 1 without any
  finiteness assumption on `K`.
