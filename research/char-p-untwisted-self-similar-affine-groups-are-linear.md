---
rg: 2
id: char-p-untwisted-self-similar-affine-groups-are-linear
kind: claim
title: Affine groups over an elementary abelian p-group whose linear parts virtually commute with a separating finite-corank endomorphism are linear over F_p[[t]]
distinct_from:
  principal-ideal-affine-groups-are-self-similar: that is Zaremsky's positive criterion making R^n x| Γ self-similar; this shows that when R has characteristic p those groups, and every untwisted virtual-endomorphism host over an elementary abelian p-group, embed in GL_N(F_p[[t]]).
  affine-self-similar-coordinate-rings-are-one-dimensional: that bounds the transcendence degree of commutative characteristic-zero coordinate domains of self-similar affine groups; this treats rings of characteristic p that need not be commutative, and proves linearity rather than a dimension bound.
  digit-affine-hosts-with-abelian-linear-parts-have-finite-rank: that bounds translation subgroups of digit-affine groups over characteristic-zero complete discrete valuation rings with virtually abelian linear parts; this linearizes affine groups over elementary abelian p-groups whose linear parts virtually commute with a separating finite-corank endomorphism, abelian or not.
  commutative-algebra-affine-groups-have-polynomial-word-problem: that bounds word problems of affine groups over commutative algebras over finite fields; this is the linearization that brings non-commutative characteristic-p self-similar hosts into its scope.
artifacts:
  - research/artifacts/fp-self-similar-hard-wp-swarm-2026-09-16.md
---

**ESTABLISHED** by `char-p-untwisted-self-similar-affine-groups-linear-proof`.
Elementary linear algebra. No novelty is claimed, and it has not been independently
reviewed.

## Setting (L)

- `p` is a prime and `A` is an elementary abelian `p`-group, that is, an
  `F_p`-vector space of any dimension.
- `ν: A -> A` is additive and injective, `A/νA` is finite of `F_p`-dimension `r`,
  and `∩_(k>=0) ν^k A = 0`.
- `End_ν(A)` is the ring of additive maps of `A` that commute with `ν`.
- For `Γ <= Aut(A)`, the product in `A x| Γ` is `(a,γ)(a',γ') = (a + γ(a'), γγ')`.

## Statement

**(a) Ring embedding.** There are an injective additive map `ι: A -> F_p[[t]]^r`
and an injective unital ring homomorphism `M: End_ν(A) -> M_r(F_p[[t]])` such that:

- `ι(e a) = M(e) ι(a)` for all `e` and `a`;
- `M(ν) = tI`;
- `a in ν^k A` iff `ι(a) in t^k F_p[[t]]^r`.

**(b) Affine groups.** Let `Γ <= Aut(A)` have a subgroup `Γ_0` of finite index `d`
whose elements commute with `ν`. Then `A x| Γ` embeds in
`GL_((r+1)d)(F_p[[t]])`. When `Γ_0 = Γ`, the map
`(a, γ) -> [[M(γ), ι(a)], [0, 1]]` is an embedding in `GL_(r+1)(F_p[[t]])`.

**(c) Zaremsky's Example 4.7 in characteristic p.** Let `R` be a unital ring with
`p·1 = 0`. Let `x in R` satisfy:

- `R/Rx` is finite, of `F_p`-dimension `s`;
- `rx = 0` implies `r = 0`;
- `∩_k R x^k = 0`.

These are the hypotheses of `principal-ideal-affine-groups-are-self-similar`. Then:

- `R` embeds as a ring in `M_s(F_p[[t]])`;
- for every `n >= 1` and every `Γ <= GL_n(R)`, the group `R^n x| Γ` embeds in
  `GL_(ns+1)(F_p[[t]])`.

**(d) Twisted hosts that reduce to (b).** Let `μ: A -> A` be additive and injective with `A/μA`
finite and `∩_k μ^k A = 0`, so that `φ = μ^(-1): μA -> A` is a surjective proper
virtual endomorphism. Let `Γ <= Aut(A)` satisfy `γ(μ^k A) = μ^k A` for all `k`.

Suppose there are:

- `m >= 1`;
- a finite-index `Γ_0 <= Γ`;
- `δ in Aut(A)` with `δ(μ^k A) = μ^k A` for all `k`,

such that `μ^(-m) γ μ^m = δ γ δ^(-1)` for every `γ in Γ_0`. Then `ν = μ^m δ`
satisfies setting (L) and commutes with `Γ_0`, so (b) applies to `A x| Γ`. Two
special cases:

- `δ = id`: the twist `γ -> φγφ^(-1)` has finite order on `Γ_0`;
- `m = 1` and `δ in Γ`: the twist is conjugation by an element of `Γ`.

## Meaning

- **Attempt 2 of `fp-self-similar-groups-with-arbitrarily-hard-word-problem`.**
  That attempt says Zaremsky's affine hosts "land inside linear groups over
  fields". For non-commutative rings this had not been proved. Part (c) proves it
  in characteristic `p`.
- **Word problems.** The consequence is
  `char-p-untwisted-affine-hosts-have-polynomial-word-problem`.

## Not covered

- **Genuinely twisted `φ`.** Here no power of `γ -> φγφ^(-1)` is virtually inner
  by a filtration-preserving automorphism. The linear parts then act on the
  completion by `F_p`-linear maps that are not `F_p[[t]]`-linear, computed by a
  transducer with infinitely many states.
- **Exponent `p^m` with `m >= 2`, or characteristic `0`.** The artifact (§9)
  sketches a reduction to affine groups over finitely generated commutative rings of
  mixed or zero characteristic. No word-problem bound for those is in the graph.
- **Non-abelian `A`, and non-surjective `φ`.**
