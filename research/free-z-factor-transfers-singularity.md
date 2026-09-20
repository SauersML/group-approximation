---
rg: 2
id: free-z-factor-transfers-singularity
kind: claim
title: The horofunction boundary of G embeds in that of G * Z as the root copy, the atoms of G * Z around root-copy points are the preimages of the atoms of G under the first-syllable map, and so every generator of G that is singular at a point in the host of G is singular at the corresponding root-copy point in the host of G * Z
requires:
  - bbmz-singularity-is-a-recurrent-coincidence
  - generalized-triangle-group-hosts-reduce-to-fixed-trees
distinct_from:
  generalized-triangle-group-hosts-reduce-to-fixed-trees: that works inside the host of G * Z (cocycle lemma, sing(t) empty); this transfers singular points from the host of G into it, which the claims about G * Z hosts built from G-host computations need.
---

**Status.**
- **ESTABLISHED** (lane proof, bh-q12-kazhdan, 2026-09-19; not reviewed). It closes the transfer gap found by
  bh-ref-c in the claims about `G ∗ Z` hosts.
- Only the direction needed for uncountability is proved. The converse is not proved and not claimed.

## Setting

- `G` is hyperbolic with finite symmetric generating set `S_G`, and `H = G ∗ ⟨t⟩` with `S = S_G ∪ {t^{±1}}`.
- Every `y ∈ H` has a normal form. `g_1(y) ∈ G` is its first `G`-syllable, which is `1` if `y` starts with a power
  of `t`.
- Word length is additive over syllables: `|h|_H = Σ |g_i|_G + Σ |e_i|`.
- Horofunctions are normalized by `η(1) = 0`.

## Lemma T

1. **The root copy.** `ι(η)(h) = η(g_1(h)) + |h| − |g_1(h)|` defines an injective, `G`-equivariant map
   `ι : ∂_h G → ∂_h H`.
2. **Atoms.** Let `y ∈ H` with `|g_1(y)| ≥ n`, and put `D = {g ∈ G ∖ B^G_{n−1} : g ~ g_1(y)}`, where `~` is the
   `B_n^G`-atom relation. Up to finitely many elements of `B^G_{n−1}`, the `B_n^H`-atom of `y` is
   `{y' : g_1(y') ∈ D}`.
   - Consequently, for `σ ∈ ∂_h G` and large `n`, the `H`-shadow at `ι(σ)` is `Z^H_n(ι σ) = π^{-1}(D) ∪ ι(Z^G_n(σ))`.
   - Here `D ⊂ G` is the set of elements of the `G`-atom, and `π(η)` is the first syllable of `η` when it is finite,
     and `ι^{-1}(η)` otherwise.
3. **Transfer.** For `s ∈ S_G`, `ι(sing_G(s)) ⊆ sing_H(s)`.

## Proof

1. **The root copy.**
   - Let `x ∈ G` and `h ∈ H`. Then `x^{-1}h = (x^{-1}g_1(h)) t^{e_1} ⋯`, and additivity gives
     `d_H(x, h) = d_G(x, g_1(h)) + |h| − |g_1(h)|`.
   - So limits of `d_H(x_k, ·)` along `x_k → σ` in `G` are the functions `ι(σ)`. Injectivity follows by restricting
     to `G`.
   - Equivariance: `g_1(s^{-1}h) = s^{-1}g_1(h)`, and the tail of `h` is unchanged.
2. **Atoms.** Let `y = g t^e w` (or `y = g`) with `|g| ≥ n`, and `h ∈ B_n^H`. If `g_1(h) ≠ g`, then `g^{-1}g_1(h) ≠ 1`
   and no `t`-syllables cancel in `y^{-1}h`. If `g_1(h) = g`, then `h = g`, since `|g| ≥ n`. In both cases
   `d_H(y, h) = |w| + |e| + d_G(g, g_1(h)) + |h| − |g_1(h)|`.
   - The last two terms depend only on `h`, and `{g_1(h) : h ∈ B_n^H} = B_n^G`. So `y ~_{B_n^H} y'` iff
     `g ~_{B_n^G} g_1(y')`.
     This holds whenever `|g_1(y')| ≥ n` too.
   - **Short first syllables with a tail are excluded.** Let `y' = g' t^e w`, with `|g'| ≤ n − 1` and `e ≠ 0`.
     Both `g't` and `g't^{-1}` lie in `B_n^H`. Then `d_{y'}(g't^{-sgn e}) − d_{y'}(g't^{sgn e}) = 2`, while the formula
     gives `0` for `y`. So `y'` is not in the atom. The remaining exceptions are the finitely many elements of
     `B^G_{n−1}`, which do not affect shadows.
   - Limits of such `y_k` either have eventually constant first syllable `g ∈ D`, or `|g_1(y_k)| → ∞`. In the second
     case the displayed formula gives the limit `ι(η_G)` with `η_G ∈ Z^G_n(σ)`. This gives the shadow formula.
3. **Transfer.** `s ∈ S_G` acts on first syllables by left multiplication. So `s π^{-1}(W) = π^{-1}(sW)` for every
   `W ⊆ G ∪ ∂_h G`, and `s ι = ι s` by part 1.
   - Suppose `s` is regular at `ι(σ)`. For large `n`, `s Z^H_n(ισ)` is an `H`-shadow containing `ι(sσ)`, so it
     equals `Z^H_k(ι sσ)` for some `k`.
   - By part 2 both sides have the form `π^{-1}(·) ∪ ι(·)`. Comparing the `ι`-parts gives `s Z^G_n(σ) = Z^G_k(sσ)`.
   - So `s` is regular at `σ` in `G`. ∎

## What it repairs

- **`racg-generators-are-singular-over-their-wall-trees`.** "The BBMZ host of `W_Petersen ∗ Z` is not bounded" now
  follows: continuum many singular points of `s` in `W`'s host give continuum many in the host of `W ∗ Z`.
- **`generalized-triangle-group-hosts-reduce-to-fixed-trees`.** Conjecture 5, stated for the host of `𝓗_31 ∗ Z`,
  follows from the same statement in `𝓗_31`'s own host, which is where Theorem D, Proposition H and the
  link-geometry computation live. So the uncountable form of Conjecture U for `𝓗_31 ∗ Z` follows from singularity
  of one generator over a Cantor set in `𝓗_31`'s own host.
- **Not repaired: the converse.** A bounded `H`-host from a bounded `G`-host is not proved. It would need control of
  `s` at points with finite first syllable. It matters only for route 2, a bounded host.
