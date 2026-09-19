---
rg: 2
id: injective-automaton-images-are-sft-cover-pairs-proof
kind: route
title: Decode a locally admissible configuration by the inverse rule and re-encode it; the window ST makes the re-encoding exact, so the image is of finite type, and gluing preimages gives strong irreducibility
target: injective-automaton-images-are-sft-cover-pairs
requires:
  - pointed-pre-injective-cover-pairs-admit-sections
artifacts:
  - research/artifacts/injective-image-sft-cover-pairs-2026-09-19.md
---

Conventions: `(g.x)(h) = x(g^-1 h)`. An automaton with memory `S` and local rule `μ` is
`τ(x)(g) = μ(h ↦ x(gh), h ∈ S)`. `Δ(x, x')` is the set of sites where `x` and `x'` differ. `L_K(Y)` is the set
of patterns `h ↦ y(gh)` on `K`, for `y ∈ Y` and `g ∈ G`. The artifact has the full write-up and calibrations.

**Step 0 (the inverse is an automaton).** `τ` is injective and continuous on a compact space, so
`ν = τ^-1 : Y → A^G` is continuous and equivariant. By the Curtis–Hedlund argument (compactness of `Y`) it has a
finite memory `T`, taken with `1 ∈ T`, and a rule `λ : L_T(Y) → A` with `ν(y)(g) = λ(h ↦ y(gh), h ∈ T)`. Extend
`λ` arbitrarily to all of `A^T`.

**Step 1 (finite type, part (a)).** Put `K = ST`, which contains `S` and `T`. Let `y ∈ A^G` have every `K`-pattern
in `L_K(Y)`. Define `z(g) = λ(h ↦ y(gh), h ∈ T)`. Fix `g`. There is `w ∈ Y` with `w(gk) = y(gk)` for all `k ∈ K`.
For `s ∈ S`, the value `z(gs)` reads `y` on `gsT ⊆ gK`, so `z(gs) = ν(w)(gs)`. Hence

```text
τ(z)(g) = μ(s ↦ z(gs)) = μ(s ↦ ν(w)(gs)) = τ(ν(w))(g) = w(g) = y(g),
```

using `1 ∈ K`. So `y = τ(z) ∈ Y`. The reverse inclusion is trivial, so `Y` is the SFT with window `K` and allowed
set `L_K(Y)`.

**Step 2 (strong irreducibility, part (b)).** Let `y_1 = τ(x_1)` and `y_2 = τ(x_2)`, and let `Ω_1, Ω_2` be finite
with `Ω_2 ∩ Ω_1 S S^-1 = ∅`. Then `Ω_1 S ∩ Ω_2 S = ∅`. Let `x` equal `x_1` on `Ω_1 S` and `x_2` elsewhere. Then
`τ(x)` agrees with `y_1` on `Ω_1` and with `y_2` on `Ω_2`. The irreducibility constant is `SS^-1`.

**Step 3 (constants, part (c)).** `τ(a^G)` is fixed by every shift, so it is a constant `b^G`. Distinct `a` give
distinct `b`, since `τ` is injective. So `a ↦ b` is a permutation of the finite set `A`, every constant lies in
`Y`, and `ν` permutes the constants. So `D = ∅`.

**Step 4 (cover pair, parts (d) and (e)).** Let `y ∈ Y`, `u = ν(y)` and `z ~ u`. Put `y' = τ(z) ∈ Y`. Then
`ν(y') = z`, and `τ(z)(g) ≠ τ(u)(g)` forces `gS ∩ Δ(u, z) ≠ ∅`. So `Δ(y, y') ⊆ Δ(ν(y), z)S^-1`, which is finite.
`ν` is a bijection `Y → A^G`, and `Y ≠ A^G` iff `τ` is not surjective.

**Step 5 (Theorem II).**
- 1 ⇒ 3 is Steps 1–4 for an injective non-surjective `τ`.
- 3 ⇒ 2: a bijective `F` is injective on `Fin_c(X)`.
- 2 ⇒ 1 is Theorem P of `pointed-pre-injective-cover-pairs-admit-sections`.

**Step 6 (Theorem III).**
- ⇐: `s = (F|_(X'))^-1 : A^G → X'` is a continuous equivariant bijection, hence an automaton, and `F ∘ s = id`.
- ⇒: let `s` be a section. `F ∘ s = id` makes `s` injective, so Steps 1–3 apply to `τ = s`. For
  `x = s(y) ∈ X' = s(A^G)`, `s(F(x)) = s(y) = x`, so `F|_(X')` is a bijection onto `A^G`. Lift-closedness with
  constant `M_s^-1` is Step 4 for `τ = s`.

**Step 7 (Corollary).**
- `CP ⇒ CP_bij` and `CP ⇒ CP_col` hold trivially.
- `CP_bij ⟺ Gottschalk` is Theorem II: a bijective pair gives condition 2, and condition 3 violates `CP_bij`.
- `Gottschalk ∧ CP_col ⇒ CP`: a counterexample to CP either is injective on `Fin_c(X)` at some constant, and then
  `G` is non-surjunctive by Theorem P, or collides at every constant, which `CP_col` forbids.
- The independence calibrations are in the claim and in the artifact, Section 4. `∎`
