---
rg: 2
id: ample-groupoid-products-expansive-iff-factors-are-proof
kind: route
title: "Proof: split a product element into a first-coordinate word followed by a second-coordinate word; refine an expansive cover of the product into rectangles and project, using pr:bebasis (3)"
target: ample-groupoid-products-expansive-iff-factors-are
requires:
  - nekrashevych-expansive-groupoid-criteria
---

Notation as in the target. "Item k" refers to the imported statements of
`nekrashevych-expansive-groupoid-criteria`, and "(3)" to condition (3) of Proposition
pr:bebasis (item 4 there). Write `X_i = 𝒢_i^{(0)}` and `𝒢 = 𝒢_1 × 𝒢_2`.

**Two standing facts.**
- (P1) Products are coordinatewise. For subsets `P_1, P_2 ⊆ 𝒢_1` and `Q_1, Q_2 ⊆ 𝒢_2`:
  - `(P_1 × Q_1)(P_2 × Q_2) = P_1P_2 × Q_1Q_2`;
  - `(P × Q)^{-1} = P^{-1} × Q^{-1}`;
  - `s(P × Q) = s(P) × s(Q)`.

  If `P, Q` are bisections, `P × Q` is a bisection, since `s = s × s` on it is a
  homeomorphism onto `s(P) × s(Q)`, and likewise for `r`. `X_i` is itself a bisection
  (`s = r = id`).
- (P2) Each `𝒢_i` has a basis of bisections (the standing definition of étale). So the
  rectangles `A × B`, with `A, B` bisections, form a basis of `𝒢`, and `𝒢` is étale with
  Cantor unit space `X_1 × X_2`.

## Item 1: compact generation

**Forward.** `S` is compact, and open when both `S_i` are, since `X_i` is open in étale
`𝒢_i`. Let `(g,h) ∈ 𝒢`. By item 1 of the import, `g = g_1⋯g_n` with
`g_k ∈ S_1 ∪ S_1^{-1}` and `h = h_1⋯h_m` with `h_l ∈ S_2 ∪ S_2^{-1}`, where `n, m ≥ 1`.
Then

`(g,h) = (g_1, r(h))⋯(g_n, r(h)) · (s(g), h_1)⋯(s(g), h_m)`.

- The first block is composable, with product `(g, r(h))` and source `(s(g), r(h))`.
- The second block is composable, with product `(s(g), h)` and range `(s(g), r(h))`.

Each factor lies in `S ∪ S^{-1}`, so `S` generates.

**Converse.** Let `S` be a compact generating set of `𝒢`, and `π_1: 𝒢 → 𝒢_1` the
projection. It is continuous and multiplicative, so `π_1(S)` is compact. Given `g ∈ 𝒢_1`,
pick any `y ∈ X_2`. Write `(g,y)` as a word in `S ∪ S^{-1}` and project: `g` is a word in
`π_1(S) ∪ π_1(S)^{-1}`. The same holds for `𝒢_2`.

## Item 2, "if"

- Let `𝒮_i` be an expansive cover of a compact open generating set `S_i` of `𝒢_i`.
- By item 1, `S = (S_1 × X_2) ∪ (X_1 × S_2)` is a compact open generating set of `𝒢`.
- `𝒮 = {F × X_2 : F ∈ 𝒮_1} ∪ {X_1 × F' : F' ∈ 𝒮_2}` is a finite cover of `S` by
  bisections (P1).

We check (3) for `𝒮`. Let `(x,y) ≠ (x',y')`, and say `x ≠ x'` (the other case is
symmetric).
- By (3) for `𝒮_1` there are words `P = F_1⋯F_n`, `P' = F'_1⋯F'_k` in `𝒮_1 ∪ 𝒮_1^{-1}`
  with `x ∈ s(P)`, `x' ∈ s(P')` and `s(P) ∩ s(P') = ∅`.
- By (P1), `P × X_2 = (F_1 × X_2)⋯(F_n × X_2)` is a word in `𝒮 ∪ 𝒮^{-1}`, because
  `X_2X_2 = X_2 = X_2^{-1}`. Its source is `s(P) × X_2`, which contains `(x,y)`.
- Likewise `(x',y') ∈ s(P' × X_2) = s(P') × X_2`, and the two sources are disjoint.

By pr:bebasis (3) ⇒ (1), `𝒮` is expansive, so `𝒢` is expansive.

## Item 2, "only if"

Let `𝒮` be an expansive cover of a compact open generating set `S` of `𝒢`.

**Step 1: refine to rectangles.**
- Each `F ∈ 𝒮` is compact and open. By (P2) it is a finite union of rectangles `A × B ⊆ F`
  with `A, B` bisections.
- Let `ℛ` be the finite family of all these rectangles. It covers `⋃𝒮 ⊇ S`, and each
  member is a bisection.

We check (3) for `ℛ`. Let `u ≠ v` be units.
- By (3) for `𝒮`, choose words `F_1⋯F_n` and `F'_1⋯F'_k` with `u ∈ s(F_1⋯F_n)`,
  `v ∈ s(F'_1⋯F'_k)`, and disjoint sources.
- Pick `γ = γ_1⋯γ_n` with `γ_i ∈ F_i` and `s(γ) = u`. For each `i` choose `R_i ∈ ℛ ∪ ℛ^{-1}`
  with `γ_i ∈ R_i ⊆ F_i`:
  - if `F_i ∈ 𝒮`, a rectangle inside `F_i` containing `γ_i`;
  - if `F_i ∈ 𝒮^{-1}`, the inverse of a rectangle inside `F_i^{-1}` containing `γ_i^{-1}`.
- Then `γ ∈ R_1⋯R_n ⊆ F_1⋯F_n`, so `u ∈ s(R_1⋯R_n) ⊆ s(F_1⋯F_n)`.
- The same construction for `v` gives a word in `ℛ ∪ ℛ^{-1}` whose source contains `v` and
  lies in `s(F'_1⋯F'_k)`. The two sources are disjoint.

So `ℛ` satisfies (3).

**Step 2: project.**
- Let `ℛ_1 = {A : A × B ∈ ℛ}`, a finite family of bisections of `𝒢_1`, and
  `S'_1 = ⋃ℛ_1`, which is compact and open.
- `π_1(S) ⊆ π_1(⋃ℛ) = S'_1`. By the converse in item 1, `π_1(S)` generates `𝒢_1`, so
  `S'_1` does too (item 1 of the import: supersets of generating sets generate).
- `ℛ_1` is a finite cover of `S'_1` by bisections.

We check (3) for `ℛ_1`. Let `x ≠ x'` in `X_1`, and fix any `z ∈ X_2`.
- By (3) for `ℛ`, there are words `R_1⋯R_n` and `R'_1⋯R'_k` whose sources contain `(x,z)`
  and `(x',z)` respectively and are disjoint.
- Write `R_i = A_i × B_i` (or its inverse, `A_i^{-1} × B_i^{-1}`). By (P1),
  `R_1⋯R_n = P × Q` with `P` a word in `ℛ_1 ∪ ℛ_1^{-1}` and `Q` a subset of `𝒢_2`.
  Similarly `R'_1⋯R'_k = P' × Q'`.
- Then `x ∈ s(P)`, `z ∈ s(Q)`, `x' ∈ s(P')` and `z ∈ s(Q')`.
- `(s(P) × s(Q)) ∩ (s(P') × s(Q')) = ∅` while `z ∈ s(Q) ∩ s(Q')`. Hence
  `s(P) ∩ s(P') = ∅`.

So `ℛ_1` is expansive by pr:bebasis, and `𝒢_1` is expansive. `𝒢_2` is symmetric (fix
`z ∈ X_1` instead).

## Item 3: the Cuntz groupoid

**Basis and bisections.**
- If `(μz, k, νz) = (μ'z', k, ν'z')` with `|μ| ≤ |μ'|`, then `μ' = μη`, `z = ηz'` and
  `ν' = νη`. So `U_{μ,ν} ∩ U_{μ',ν'}` is `U_{μη,νη}` or empty, and the `U_{μ,ν}` form a
  basis.
- `z ↦ (μz, |μ|-|ν|, νz)` is a continuous bijection from `X` onto `U_{μ,ν}`: the preimage
  of `U_{μη,νη}` is the cylinder `[η]`. So `U_{μ,ν}` is compact.
- `s` and `r` restrict to homeomorphisms `U_{μ,ν} → [ν]` and `U_{μ,ν} → [μ]`. So
  `U_{μ,ν}` is a bisection, and `G_2` is étale with unit space `U_{∅,∅} ≅ X`.

**Generation.** `U_{μ,∅} = {(μz, |μ|, z)}`.
- `U_{μ,∅} = U_{μ_1,∅}⋯U_{μ_n,∅}` by induction on `n`. With `μ = μ_1μ'`, the product
  `(μ_1 y, 1, y)(μ'z, |μ'|, z)` is defined iff `y = μ'z`, and it equals `(μz, |μ|, z)`.
- `U_{μ,ν} = U_{μ,∅}U_{ν,∅}^{-1}`, since `(μz, |μ|, z)(z, -|ν|, νz) = (μz, |μ|-|ν|, νz)`.
- `U_{∅,∅} = U_{0,∅}^{-1}U_{0,∅}`.

So `S = U_{0,∅} ∪ U_{1,∅}`, which is compact and open, generates `G_2`.

**Expansive cover.** `𝒮 = {U_{0,∅}, U_{1,∅}}`. For a word `ν` of length `k ≥ 1`,
`U_{ν,∅}^{-1} = U_{ν_k,∅}^{-1}⋯U_{ν_1,∅}^{-1}` is a word in `𝒮^{-1}`, with source
`r(U_{ν,∅}) = [ν]`. If `z ≠ z'` first differ at position `k`, their length-`k` prefixes
`ν ≠ ν'` give disjoint sources `[ν] ∋ z` and `[ν'] ∋ z'`. This is (3), so `𝒮` is expansive.

## Item 4: the host family

- `Γ` has a finite generating set `E = E^{-1}`. Then `E × M` is compact and open, and
  generates `Γ × M`: `(e_1⋯e_n, x) = (e_1, e_2⋯e_n x)⋯(e_n, x)`, and units are `(1,x)`,
  obtained as `(e,x)^{-1}(e,x)`.
- By item 1 and item 3, `(M ⋊ Γ) × G_2` is compactly generated.
- By item 2 and item 3, it is expansive iff `M ⋊ Γ` is expansive.
- By Proposition pr:expansivegroups (item 6 of the import, (1) ⇔ (4)), this holds iff
  `Γ ↷ M` is a subshift. `Γ` is finitely generated and `M` is a Cantor set, as that
  proposition requires.
