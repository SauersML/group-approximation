---
rg: 2
id: post-surjective-decoders-convert-strict-pairs-to-dual-failures
kind: claim
title: A strict automaton pair with a post-surjective decoder is exactly a post-surjective, non-pre-injective automaton with a cellular right inverse
distinct_from:
  linear-strict-pairs-are-transposes-of-post-surjective-automata: that dualizes a linear strict automaton through its transpose over a field; this converts arbitrary nonlinear strict pairs through their decoders, and isolates post-surjectivity of the decoder as the one missing input.
  split-decoders-have-generic-cantor-fibers: that proves a split decoder is pre-injective only when bijective, and packs Cantor fibers; this adds the post-surjective side, the affine case, the exclusion over dual surjunctive groups, and the periodic-fiber condition on cellular right inverses.
artifacts:
  - research/artifacts/gk3-dual-surjunctivity-2026-09-14.md
---

**ESTABLISHED (elementary; no novelty claimed).**

**Setting.** `G` is a group and `A` a finite alphabet. An **automaton** is a
continuous `G`-equivariant map `A^G -> A^G`. Configurations are
**asymptotic**, `x ~ x'`, if they differ on a finite set.
- An automaton `F` is **pre-injective** if `x ~ x'`, `x != x'` always gives
  `F(x) != F(x')`.
- `F` is **post-surjective** (Capobianco–Kari–Taati) if for every `x` and
  every `y' ~ F(x)` there is `x' ~ x` with `F(x') = y'`.
- A **strict pair** is an injective, non-surjective automaton `τ` with a
  **decoder**: an automaton `σ` with `σ∘τ = id`. Write `Y = τ(A^G)`.

**Theorem.**
1. **(a) Conversion.** `G` carries a strict pair whose decoder is
   post-surjective iff `G` carries a post-surjective, non-pre-injective
   automaton `μ` with an automaton right inverse `ν` (`μ∘ν = id`). Forward,
   `μ = σ` and `ν = τ`; backward, `(ν, μ)` is a strict pair.
2. **(b) Post-surjectivity at points near the image.** Every decoder `σ` is
   post-surjective at each `x` whose asymptotic class meets `Y`.
3. **(c) Affine decoders.** If `A` is a finite abelian group and
   `σ = L + c` with `L` a continuous equivariant group endomorphism of `A^G`
   and `c` a constant configuration, then `σ` is post-surjective, whatever
   the encoder `τ` is. This is the argument of Doucha–Gismatullin for the
   linear case, extended to affine maps.
4. **(d) Exclusion.** If `G` is dual surjunctive (every post-surjective
   automaton over `G` is pre-injective, over every finite alphabet), no
   strict pair over `G` has a post-surjective decoder; in particular none has
   an affine decoder. By Capobianco–Kari–Taati this covers all sofic groups.
5. **(e) Exact gap of (b).** For a strict pair over an infinite group, some
   configurations have asymptotic classes disjoint from `Y`: any `x` carrying
   a Garden-of-Eden pattern of `τ` at infinitely many pairwise disjoint
   translates of its support.
6. **(f) Periodic-fiber condition on right inverses.** If `μ` has an
   automaton right inverse, then for every subgroup `H <= G`, `μ` maps the
   `H`-fixed configurations onto the `H`-fixed configurations. In particular
   `μ` permutes the constant configurations.

So a nonlinear Gottschalk counterexample refutes dual surjunctivity for the
same group as soon as its decoder can be chosen post-surjective
(`strict-pairs-admit-post-surjective-decoders`). A dual-surjunctivity
counterexample refutes Gottschalk for the same group as soon as it admits a
cellular right inverse (`post-surjective-automata-admit-automaton-right-inverses`),
and (f) is a necessary condition for that.

The route is `post-surjective-decoder-conversion-proof`.
