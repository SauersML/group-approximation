---
rg: 2
id: euclidean-building-lattices-f-infinity-simple-host-proof
kind: route
title: The unrescaled box orbit category of a Euclidean building lattice is a Li-Garside degree category with finite units; sector codings resynchronize, the uniform box measure shows shadows of loops shrink, and Ciobotaru–Le Bars gives minimality, so the Cuntz host theorem applies
target: euclidean-building-lattices-embed-in-f-infinity-simple-groups
requires:
  - euclidean-building-lattices-lie-in-permutational-bh-class
  - cuntz-garside-coded-actions-embed-in-f-infinity-simple-groups
---

**Lane proof, not independently reviewed.** Notation is that of
`euclidean-building-lattices-lie-in-permutational-bh-class` (below, "the building node"), Steps
0–2 and 5. We check (C1)–(C4) of `cuntz-garside-coded-actions-embed-in-f-infinity-simple-groups`
(below, "the host theorem") for `𝔠 = ℭ_Γ`, with no rescaling. Its Steps 3, 4 and 6 are not used.
- `r` is the rank.
- `d : ℭ_Γ → N^r` is the box shape.
- Morphisms are pairs `(p,γ)`.
- The units are `(i_a,k)`, `k ∈ K_a` (finite tile stabilizers).
- `X = ∂Ω(ℭ_Γ)` is the space of sectors issuing from the representative tiles.

## (C1) Li's standing hypotheses

From Step 1 of the building node: `ℭ_Γ` is left and right cancellative, has finite units (the
morphisms of degree 0), is locally finite, and satisfies (UFP*). By the composition lemma, it
is finitely aligned with finite disjoint mcms. Right cancellation gives (F). It remains to
check the Garside family, directly.

**The family.** Let `𝔖 = d^{-1}({0,1}^r ∖ 0)`, one morphism per right unit class. It is locally
finite and `=*`-transverse, and it avoids the units.

**Normal forms.** For `a` of degree `n`, let `δ_i ∈ {0,1}^r` be the indicator of
`{j : n_j ≥ i}` (`i = 1, …, max n_j`). By (UFP*) we have `a = s_1 ⋯ s_L` with `d(s_i) = δ_i`,
unique up to units between the factors.
- **Normality.** Let `t ∈ 𝔖` with `t ≼ s_i s_{i+1}`, of degree `δ ≤ δ_i + δ_{i+1}`,
  `δ ∈ {0,1}^r`. Wherever `δ_{i+1}` is 1, so is `δ_i`. So `δ ≤ δ_i`.
- By (UFP*), `t` is the degree-`δ` prefix of `s_i s_{i+1}`, which is the degree-`δ` prefix of
  `s_i`. So `t ≼ s_i`.

So `𝔖` is a Garside family (Li's definition, `s:CatBisGar`).

**Norm.** `‖a‖ = max_j d(a)_j`. Left divisors have smaller degrees, so every `(𝔖^{≤L})^♯` is
closed under left divisors.

**Boundary.** `∂Ω = X` is closed and invariant. It has no sinks, since every tile has
successors in every colour, so `X ⊆ Ω_∞`.

## (C2) Every element is a global bisection

This is Step 2 of the building node: `[O,γω)` and `γ[O,ω)` share a subsector, so `γ` is a
finite union of basic bisections, and it acts faithfully. The unit space there is the
amplification `Y_D ⊆ X × D`, where `D` is the finite set of tiles at the base vertex. Two
remarks put this in the form (C2) needs.
- **Amplification is absorbed by the Cuntz factor.** A complete prefix code
  `{w_d : d ∈ D} ⊆ {x,y}^*` gives an isomorphism `(𝒢 × R_D) × G_2 ≅ 𝒢 × G_2`, via
  `(ξ, d, z) ↦ (ξ, w_d z)`. So `Y_D × C` becomes a compact open `Z ⊆ X × C`.
- **`Z` compresses into one cone.** By comparison in the purely infinite minimal groupoid
  `𝒢 × G_2` (host theorem, §2 of its proof), `Z` is carried by a compact open bisection into
  `X(v_0) × C`. Conjugating and extending by the identity embeds `F((𝒢×G_2)|_Z)` in
  `S = F((𝒢×G_2)|_{X(v_0)×C})`.

Then `g ↦ g × id` followed by this embedding puts `Γ` in `S`. Faithfulness is Step 2 of the
building node, and injectivity follows because the maps involved are group embeddings.

## (C3) Shadows shrink

**Counts.** From Step 3 of the building node:
- a tile's number of `j`-successors depends only on its phase;
- a `j`-step moves the phase deterministically.

Hence the number `N_a(n)` of boxes of shape `n` from `i_a` (modulo right units) is a product
of phase counts along any factorization. By (UFP*), each box `λ` of shape `n` has exactly
`N_a(n+n')/N_a(n)` extensions of shape `n + n'`.

**Lower bound.** Thickness gives at least two successors in each colour: a `j`-successor is a
chamber at a fixed nontrivial Weyl distance from the far chamber, and there are
`q_{w} ≥ 2` of them. So `N_a(n) ≥ 2^{|n|}`.

**The measure.** The cylinders `λ∂Ω`, `λ ∈ i_a ℭ_Γ^n`, partition `∂Ω(a)` for each `n`, and
refine consistently. So `μ_a(λ∂Ω) = 1/N_a(d(λ))` defines a Borel probability measure on
`∂Ω(a)`, the uniform box measure (Carathéodory).

**The argument.** Let `σ ∈ ℭ_Γ(a,a)` be a non-unit, so `m = d(σ) ≠ 0`.
- For every `k`, `μ_a(σ^k ∂Ω) = 1/N_a(km) ≤ 2^{−k|m|}`.
- A nonempty open subset of `∂Ω(a)` contains a cylinder `λ∂Ω`, which has measure `1/N_a(d(λ)) > 0`.
- If `λ∂Ω ⊆ ∩_k σ^k∂Ω`, then `1/N_a(d(λ)) ≤ 2^{−k|m|}` for all `k`, which is impossible.

So `∩_k σ^k ∂Ω(a)` has empty interior, and (C3) holds.

## (C4) Minimal, effective, Hausdorff

- **Minimal.** Let `U` be a nonempty open subset of a cone `∂Ω(a)`, and `x ∈ X` a sector with
  chamber at infinity `ω_x`.
  - `U` contains the cylinder of a box `λ` from `i_a`. The chambers at infinity whose sector
    from the base of `i_a` begins with `λ` form a nonempty open set `O`.
  - By Ciobotaru–Le Bars minimality (Proposition `prop minimal`, as quoted in the building
    node), some `γω_x ∈ O`. Then the sector from `i_a` to `γω_x` lies in `U`.
  - That sector is tail-equivalent to `γx`, hence in the `𝒢`-orbit of `x`.

  So `𝒢` is minimal on `X`, hence on every clopen reduction.
- **Effective.** This is Step 5 of the building node (Ciobotaru–Le Bars topological freeness).
- **Hausdorff.** If a basic germ `[λμ^{-1},χ]` were a unit germ, there would be `y` with
  `λy = μy`. Right cancellation then gives `λ = μ`. So unit-germ sets of basic bisections are
  empty or everything, and the groupoid is Hausdorff.
- **Perfect.** `X` has no isolated points, since thickness makes every cylinder split.

## Conclusion

(C1)–(C4) hold. By the host theorem, `S` is simple of type `F_∞`, and `Γ ↪ S` by (C2). Item 4
of the host theorem gives commensurability closure, via normal cores and `S ≀ Q ≤ S`. ∎

## Lesson for general BH

For building lattices, finiteness needs no loop condition once the Cuntz factor is present.
Li's `(t<d)` forced the rescaling to two loops per colour and the phase skew product, and those
steps were also what obscured minimality. Without them, the only dynamical input is minimality
on chambers at infinity. The only combinatorial input beyond the box calculus is that shadows
of loops shrink, which a uniform counting measure proves in three lines.

This is a general mechanism: in any coding with at least two successors per colour, a counting
measure proves (Acyc).
