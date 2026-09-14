---
rg: 2
id: post-surjective-decoder-conversion-proof
kind: route
title: Read the decoder as the post-surjective map, lift finite changes through the encoder, and test right inverses on fixed points
target: post-surjective-decoders-convert-strict-pairs-to-dual-failures
requires:
  - split-decoders-have-generic-cantor-fibers
  - capobianco-kari-taati-dual-surjunctivity-toolkit
artifacts:
  - research/artifacts/gk3-dual-surjunctivity-2026-09-14.md
---

Notation as in the target. Automata have finite memory, so `x ~ x'` implies
`F(x) ~ F(x')` for every automaton `F` (used throughout).

**(a) Forward.** Let `(τ, σ)` be a strict pair with `σ` post-surjective.
- `σ` is not bijective: otherwise `τ = σ^(-1)` is surjective.
- `σ∘τ = id` and `σ` is not bijective, so `σ` is not pre-injective by
  `split-decoders-have-generic-cantor-fibers`.
- `τ` is an automaton right inverse of `σ`.

**(a) Backward.** Let `μ` be post-surjective and not pre-injective, with
`μ∘ν = id`.
- `ν` is injective, since `μ∘ν = id`.
- If `ν` were surjective, it would be bijective with inverse `μ`. Then `μ`
  would be injective, hence pre-injective: a contradiction.
- So `(ν, μ)` is a strict pair, and its decoder `μ` is post-surjective.

**(b).** Let `x'' ∈ Y` with `x'' ~ x`, and let `y' ~ σ(x)`.
- Write `x'' = τ(w)`. Then `τσ(x'') = τστ(w) = τ(w) = x''`.
- `σ(x'') ~ σ(x) ~ y'`, so `x' := τ(y') ~ τσ(x'') = x'' ~ x`.
- `σ(x') = στ(y') = y'`.

**(c).** Let `σ = L + c` and `y' ~ σ(x)`. Put `x' = x + τ(y') - τ(σ(x))`.
- `τ(y') ~ τ(σ(x))`, so `x' ~ x`.
- `σ(x') = L(x) + L(τ(y')) - L(τ(σ(x))) + c`. Since `σ∘τ = id` gives
  `L∘τ = id - c`, this equals `L(x) + (y' - c) - (σ(x) - c) + c = y'`.
- Nothing about `τ` beyond `σ∘τ = id` is used. For linear `σ` over a finite
  field this is the Claim in the proof of Doucha–Gismatullin's Theorem
  (arXiv:2008.10565, pinned in `capobianco-kari-taati-dual-surjunctivity-toolkit`).

**(d).** Suppose `G` is dual surjunctive and `(τ, σ)` is a strict pair with
`σ` post-surjective.
- Then `σ` is pre-injective.
- By (a, forward) `σ` is not pre-injective: a contradiction.
- Affine decoders are post-surjective by (c), so they are excluded too.
- Sofic groups are dual surjunctive (Capobianco–Kari–Taati, pinned in the
  import).

**(e).** Let `τ` be injective and not surjective, over an infinite `G`.
- `Y` is closed and invariant and misses some configuration. So some finite
  pattern `p : D -> A` occurs in no element of `Y`: a Garden-of-Eden pattern.
- Choose `g_1, g_2, ...` with the translates `g_i D` pairwise disjoint;
  possible since `G` is infinite. Let `x` carry the translate of `p` on every
  `g_i D`.
- Any `x' ~ x` still carries the translate of `p` on all but finitely many
  `g_i D`. Since `Y` is invariant and forbids `p`, `x' ∉ Y`. So the class of
  `x` misses `Y`.
- Over a finite group every injective automaton is surjective, so strict
  pairs need infinite `G`.

**(f).** Let `μ∘ν = id` and let `y` be `H`-fixed.
- `ν(y)` is `H`-fixed by equivariance, and `μ(ν(y)) = y`. So the image of the
  `H`-fixed set under `μ` contains every `H`-fixed configuration.
- Equivariance gives the reverse inclusion.
- For `H = G` the fixed configurations are the `|A|` constants. A surjection
  of a finite set onto itself is a bijection.
