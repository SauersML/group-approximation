---
rg: 2
id: cp-is-equivalent-to-its-colliding-fragment-proof
kind: route
title: Run the non-pre-injectivity step of the bounded-defect proof with a constant base point; every constant lies in the image, so the route pair collides at every constant
target: cp-is-equivalent-to-its-colliding-fragment
requires:
  - strict-pairs-give-dual-failures-on-bounded-defect-domains
  - pointed-pre-injective-cover-pairs-admit-sections
  - injective-automaton-images-are-sft-cover-pairs
artifacts:
  - research/artifacts/bounded-defect-domain-duality-2026-09-17.md
---

Notation as in `bounded-defect-domain-dual-failure-proof`: `(τ, σ)` is a strict pair on `A^G`, `Y = τ(A^G)`,
`E = τ∘σ`, `M` is a memory of `τ`, `W ⊇ {1} ∪ M ∪ PP⁻¹P ∪ W_E` (`W_E` a memory of `E`), `p ∈ A^P` a pattern
occurring in no point of `Y`, and `R ≥ |P||W|`. `D(x)` is the defect set.

**Step 1. `X_R` is a proper SI SFT cover pair with section `τ`.** This is items 1, 2, 3 and 5 of
`strict-pairs-give-dual-failures-on-bounded-defect-domains`, all holding at once by its Assembly.

**Step 2. Every constant lies in `Y ⊆ X_R`, and `D = ∅`.** Since `τ` is equivariant, `τ(b^G)` is fixed by every
shift, hence a constant `φ(b)^G`. `τ` is injective, so `φ : A → A` is injective, hence a permutation of the
finite set `A`. So every constant `c^G` equals `τ(φ⁻¹(c)^G) ∈ Y`, and `Y ⊆ X_R` by item 1. The constant map of
`σ|_{X_R}` is `c ↦ φ⁻¹(c)`, since `σ(τ(b^G)) = b^G`, and it is onto. So `D = ∅`. (This is also Theorem I(c) of
`injective-automaton-images-are-sft-cover-pairs`.)

**Step 3. Collision at a prescribed constant `c^G`.** Run step 4 of `bounded-defect-domain-dual-failure-proof`
with `y0 = c^G`, which is allowed because `c^G ∈ Y` by Step 2. That step takes any `y0 ∈ Y`.
- Let `x1` equal `p` on `P` and `c` off `P`. As shown there, `D(x1) ⊆ PW⁻¹`, so every defect component has at
  most `|P||W| ≤ R` sites. So `x1 ∈ X_R`, and `x1 ∉ Y`.
- Put `x2 = E(x1) ∈ Y ⊆ X_R`. By the center rule (F1), `x2 = x1` off the finite set `D(x1)`.
- `x1` differs from `c^G` only on `P`. So `x1, x2 ∈ Fin_c(X_R)`, `x1 ≠ x2` (one is in `Y`, the other is not),
  and `σ(x2) = στσ(x1) = σ(x1)`.

So `σ|_{X_R}` is not injective on `Fin_c(X_R)`. `c` was arbitrary. This proves the Theorem.

**Corollary 1.**
- `CP_col(G) ⇒ Gottschalk(G)`: if `G` is not surjunctive, it carries a strict pair (Assembly, last bullet of the
  cited proof). Then the Theorem gives a proper constant-point SFT pair colliding at every constant.
- `CP_col ⇒ CP`: let `(X, F)` be a proper constant-point SFT cover pair over `G`.
  - If `G` is not surjunctive, the previous bullet contradicts `CP_col`.
  - If `G` is surjunctive, then `F` collides at every constant of `X`. Otherwise `F` is injective on some
    `Fin_c(X)`, and Theorem P of `pointed-pre-injective-cover-pairs-admit-sections` makes `G` non-surjunctive.
    This again contradicts `CP_col`.
- `CP ⇒ CP_col^∃ ⇒ CP_col`: the first holds because CP forbids every pair. The second holds because a
  constant-point pair has at least one constant, so colliding at every constant implies colliding at some
  constant.

**Corollary 2.**
- **Sectioned pairs force non-surjunctivity.** Let `s` be a section of a proper pair. `s` is continuous and
  equivariant, hence an automaton (Curtis–Hedlund–Lyndon). It is injective because `F ∘ s = id`. It is not
  surjective because `s(A^G) ⊆ X ≠ A^G`.
- **⇐.** At a surjunctive `G` every pair is therefore sectionless, and `CP_nosec` forbids it.
- **⇒.** `CP ⇒ Gottschalk` is `gottschalk-via-constant-point-domains`, and `CP ⇒ CP_nosec` is trivial.
- **Sectionless pairs collide everywhere.** This is the contrapositive of Theorem P.

**Class kill.** Each listed profile property holds for `(X_R, σ)`:
- strong irreducibility, by item 1;
- `D = ∅` and containing every constant, by Step 2;
- colliding at every constant, by Step 3;
- non-pre-injectivity, by Step 3;
- large `Φ` and windows, since `W` and `R` may be enlarged freely.

So the restricted CP refutes `(X_R, σ)` at every non-surjunctive group, i.e. it implies Gottschalk.
