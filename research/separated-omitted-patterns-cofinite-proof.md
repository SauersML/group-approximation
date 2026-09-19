---
rg: 2
id: separated-omitted-patterns-cofinite-proof
kind: route
title: Restrict to the letters that survive, then regroup over a subgroup separating the omitted pattern so the pattern becomes a letter
target: separated-omitted-patterns-make-nonsurjunctive-sizes-cofinite
requires:
  - transition-digraph-capacity-lifts-give-nonsurjunctive-sizes
  - surjunctivity-passes-to-subgroups
  - surjunctivity-is-a-commensurability-invariant
---

Complete proof. Notation as in the target. `τ(x)(g) = μ((g^(-1)x)|_M)` with `1 ∈ M`, and `(k.x)(g) = x(k^(-1)g)`.

## Imports, verbatim

- `transition-digraph-capacity-lifts-give-nonsurjunctive-sizes`, item 2: "If `U` is an upset with `b = |U|` and
  `z = k - b`, then `bm + zs ∈ NS(G)` for all `1 <= s <= m`." There, an upset is "`U ⊆ A` closed under `R(τ)`", with
  `R(τ) = {(x(g), τ(x)(g)) : x ∈ A^G, g ∈ G}`.
- `surjunctivity-passes-to-subgroups`, proof: "The *same* memory and rule define a cellular automaton `tau^G` over
  `G` [...] on each left coset `gH` the map `tau^G` acts as a copy of `tau` transported by `h -> gh`. So `tau^G` is
  injective [...] reading off any single coset shows `tau` is surjective." Since the copy is the same alphabet, a
  strict automaton over `H` on `n` letters gives a strict one over `G` on `n` letters. So `NS(H) ⊆ NS(G)` for
  every `H <= G`.
- `surjunctivity-is-a-commensurability-invariant`, route `surjunctivity-commensurability-invariance-proof`, items 1
  and 2: "For `G = ⊔_i H r_i`, the map `Φ(x)(h) = (x(h r_i))_(i<=n)` is a homeomorphism `A^G -> (A^n)^H`. It
  intertwines the left `H`-shifts [...] So `Φ τ Φ^-1` is a continuous, equivariant, injective self-map of
  `(A^n)^H`, and by Curtis–Hedlund–Lyndon it is an automaton over `H`."

## Item 1. Omitted letter

Suppose no image configuration takes the value `b` anywhere. Put `A' = A \ {b}`.

**Restriction.** `τ` maps `A'^G` into `τ(A^G) ⊆ A'^G`, by the same rule restricted to `A'^M`. So it is a cellular
automaton over `G` on `k - 1` letters. It is injective. Suppose it were onto `A'^G`. Take any `x ∈ A^G`. Then
`τ(x) ∈ A'^G = τ(A'^G)`, so `τ(x) = τ(y)` with `y ∈ A'^G`, and injectivity gives `x = y ∈ A'^G`. Hence
`A^G = A'^G`, which is false since `b ∈ A`. So the restriction is strict, and `k - 1 ∈ NS(G)`.

**Upset.** No pair of `R(τ)` ends at `b`. So `U = A'` is closed under `R(τ)`, an upset with `|U| = k - 1` and
`z = 1`. The imported item 2 gives `(k-1)m + s ∈ NS(G)` for `1 <= s <= m`.
- For `m >= k - 1`, the values `s = 1, ..., k-1` cover the whole interval `[(k-1)m + 1, (k-1)(m+1)]`.
- These intervals tile `[(k-1)^2 + 1, ∞)`.

So `NS(G)` contains every `n >= (k-1)^2 + 1`, including `2^j` for all large `j`.

Also `{b}` is a class of `R(τ)` of size `1`, since nothing returns to `b`, so `g(τ) = 1`. Note that `k >= 3`,
because an injective image inside `A'^G` needs `|A'| >= 2`. Otherwise `A'^G` is a single point and `A^G` is not.

## Item 2. Separated omitted pattern

Let `w ∈ A^F` be omitted. The points of `F` lie in distinct right cosets `Hf`, so there is a right transversal
`T ⊇ F` with `G = ⊔_{t ∈ T} Ht`, and `|T| = [G : H] < ∞`. Put `Φ(x)(h) = (x(ht))_{t ∈ T}`. By the import,
`τ̂ = Φ τ Φ^(-1)` is an injective automaton over `H` on the alphabet `A^T`. It is not surjective, because `Φ` is a
bijection and `τ` is not onto.

Let `ℓ ∈ A^T` with `ℓ|_F = w`. Suppose `τ̂(Φ(x))(h) = ℓ` for some `x` and `h`. Then `τ(x)(ht) = w(t)` for `t ∈ F`,
that is, `(h^(-1).τ(x))|_F = w`. So `w` appears in a translate of an image configuration, a contradiction. Hence
`τ̂` omits the letter `ℓ`. Item 1 over `H` makes `NS(H)` cofinite, and the subgroup import gives
`NS(H) ⊆ NS(G)`.

## Item 3. Criterion

- If `H` separates `F`, then `f f'^(-1) ∉ H ⊇ K(G)` for `f ≠ f'`, so `F F^(-1) ∩ K(G) = {1}`.
- Conversely, for each of the finitely many pairs `f ≠ f'`, the element `f f'^(-1) ∉ K(G)` avoids some
  finite-index `H_{f,f'}`. The intersection `H` of these has finite index and contains none of them.
- `K(G)` is normal, because conjugation permutes the finite-index subgroups.

## Item 4. Ball form

**Restriction to `H_0 = ⟨M ∪ F⟩`.**
- Since `M ⊆ H_0`, `A^G` is the product over left cosets `gH_0` of copies of `A^(H_0)`, and `τ` acts as one copy
  `τ_0` on each factor.
- `τ_0` is injective. If `τ_0(u) = τ_0(u')`, extend `u` and `u'` by the same values off `H_0`. The images agree,
  so `u = u'`.
- The image of `τ_0` is the set of restrictions to `H_0` of image configurations of `τ`. So `τ_0` omits `w` on
  `F ⊆ H_0`, and in particular it is not surjective.

Rename `H_0` as `G`.

**Finite certificates.**
- `τ` is a homeomorphism of the compact space `A^G` onto its image `X`. The map `y -> τ^(-1)(y)(1)` is continuous
  on `X`, so it depends only on `y|_N` for some finite `N`.
- Let `ν : A^N -> A` be that function on the `X`-patterns, extended arbitrarily to the rest. Since
  `τ(x)(n) = μ(m -> x(nm))`, we get:
  - (C1) `ν( (μ(m -> u(nm)))_{n ∈ N} ) = u(1)` for every `u ∈ A^(NM)`. Every `u` extends to some `x`, and the
    left side is then `τ^(-1)(τ x)(1) = x(1)`.
  - (C2) `(μ(m -> u(fm)))_{f ∈ F} ≠ w` for every `u ∈ A^(FM)`.
- Both conditions mention only `μ`, `ν`, `w`, and the multiplication maps `N × M -> NM` and `F × M -> FM`.

**Transfer.**
- Let `r` bound the `S`-word lengths of the elements of `M ∪ N ∪ F`, and take `L >= 4r`.
- The quotient `π : G_L -> G` is a homomorphism. It is injective on the ball of radius `L/2`: if words `u, v` of
  length `<= L/2` have `π(u) = π(v)`, then `uv^(-1)` has length `<= L` and is trivial in `G`, so it is a relator
  of `G_L`.
- Lift `M`, `N`, `F` along `π` inside the `r`-ball. The products `ñ m̃` and `f̃ m̃` lie in the `2r`-ball, where
  `π` is a bijection onto the corresponding elements of `G`. So the lifted multiplication maps, including all
  coincidences `ñ m̃ = ñ' m̃'`, match those of `G`, and (C1) and (C2) hold verbatim over `G_L`.

**Consequences over `G_L`.**
- Let `τ̃` and `σ` be the automata over `G_L` with rules `μ` on `M̃` and `ν` on `Ñ`.
- Apply (C1) to `(g^(-1)x)|_(ÑM̃)`. This gives `σ(τ̃ x)(g) = x(g)`, so `τ̃` is injective.
- (C2) says `w` does not occur on `F̃` in any image configuration. The image is shift-invariant, so `w` occurs in
  no translate either. Hence `τ̃` is strict over `G_L` on `k` letters and omits `w ∈ A^F̃`.
- If `F̃ F̃^(-1) ∩ K(G_L) = {1}`, items 2 and 3 over `G_L` give `2^j ∈ NS(G_L) ⊆ NS_all` for all large `j`. This is
  the conclusion of `some-nonsurjunctive-group-gives-a-binary-power-one`.
- The same argument applies to any group whose `2r`-ball, as a marked partial group, matches that of `G`. The
  contrapositive in the target is the negation of this.

## Item 5. No compression

Let `σ : A^G -> B^G` be an injective automaton with `B ⊊ A`, identifying `B` with a subset of `A`. Then
`τ = ι ∘ σ` is an injective automaton on `A^G` whose image misses the letters of `A \ B`. It is strict. By item 1,
`2^j ∈ NS(G)` for large `j`, which contradicts `every-group-is-surjunctive-over-binary-power-alphabets`. The other
two bullets follow in the same way from items 1 and 2.

## The limits

- **`K = G`.** A separating `H` has finite index, so `H = G`. Then `f f'^(-1) ∉ G` is impossible for `|F| >= 2`.
- **Overgroups.** If `G <= G'` and `H' <= G'` has finite index and separates `F`, then `H' ∩ G` has index at most
  `[G' : H']` in `G`. It separates `F`, since `f f'^(-1) ∈ G \ H'`.
- **Soficity.** `G_L` carries a strict automaton, so it is not surjunctive. Hence it is not sofic (Gromov–Weiss),
  and in particular not residually finite, so `K(G_L) ≠ 1`.
