---
rg: 2
id: monotone-automata-with-a-pinned-bracketing-star-are-onto
kind: claim
title: A monotone injective automaton is onto when some minimal letter has a rigid up-set that bounds every letter from above
distinct_from:
  monotone-injective-chain-automata-are-translations: that kills chains, where every pair is comparable; this kills posets with incomparable letters that have no meets or joins, such as the bowtie and short fences, by reading off one preserved letter.
  monotone-strict-automata-ascend-along-poset-homs: that is the ascent and names the survivors; this removes a class of connected survivors, including crowns of four and fences of up to five letters.
  finite-injective-charge-noncreation-forces-surjectivity: that is the charge tool; this is the observation that one letter preserved up to a translation already gives unit-charge nonincrease, and a monotone way to produce such a letter.
  monotone-binary-injective-rules-are-copies: that is the two-letter case; this works on alphabets where most letters are pairwise incomparable.
artifacts:
  - experiments/monotone-connected-posets-2026-09-17/search_z.py
  - experiments/monotone-connected-posets-2026-09-17/search_z_results.txt
---

**ESTABLISHED** by `monotone-automata-with-a-pinned-bracketing-star-are-onto-proof`, from
`monotone-injective-chain-automata-are-translations` and `finite-injective-charge-noncreation-forces-surjectivity`.

Let `G` be any group, `L` a finite poset and `ρ` an injective automaton on `L^G` that is monotone
(`x <= x'` sitewise implies `ρ(x) <= ρ(x')`). Write `x_t(h) = x(ht)`. Call a finite poset `K` *pinned* if every
monotone injective automaton on `K^G` that fixes every constant configuration is `x ↦ x_t` for one `t ∈ G`.

**Theorem.**
1. **One preserved letter suffices.** Let `τ` be any injective automaton on `L^G` (no order needed) and `q ∈ L`
   with `τ(q^G) = q^G`. If for some `t ∈ G`, `x(h) = q` implies `τ(x)(ht^{-1}) = q` for all `x` and `h`, then `τ`
   is surjective, and in fact `τ(x)(ht^{-1}) = q` if and only if `x(h) = q`.
2. **Pinned posets.** Chains are pinned. If `A` is a nonempty antichain, then `⊥ + A` (a least letter below the
   antichain) and `A + ⊤` are pinned.
3. **Bracket criterion.** Suppose `L` has a minimal letter `m` such that the up-set `↑m` is pinned and every letter
   of `L` has a common upper bound with `m`. Then `ρ` is surjective. Dually, the same holds with a maximal letter
   `q` whose down-set `↓q` is pinned and which has a common lower bound with every letter.

**Corollaries.** Each of the following alphabets carries no monotone strict automaton, over any group.
- Every connected height-one poset in which one letter is comparable with every letter of the other level.
  Examples are the complete bipartite orders `K_{p,q}` (the bowtie, or crown of four, is `K_{2,2}`), `V`, `Λ`, `N`,
  every fence of at most five letters, and every "fan" in which one minimal letter lies below all maximal ones.
- Every poset with a greatest letter and a minimal letter whose up-set is a chain. Dually, every poset with a
  least letter and a maximal letter whose down-set is a chain. The shape of the rest of the poset is arbitrary.
- Every poset with a minimal letter `m` whose strict up-set is an antichain of maximal letters, when every letter
  lies below one of those maximal letters.

**What this changes.**
- In the ascent `monotone-strict-automata-ascend-along-poset-homs`, the surviving alphabets were the connected
  non-chains. A parallel lane (swarm-0917 gs-alt, reported on the bus) kills products of chains and lattices glued
  at a letter with chain-product ideal and filter. Those arguments need meets and joins. This one needs none: the
  bowtie and short fences, which gs-alt listed as survivors, die here.
- The invariant is a single letter preserved up to translation. Item 1 turns that into unit-charge nonincrease, and
  item 3 produces it from one rigid up-set that reaches every letter. The method fails exactly when no rigid star
  of a letter bounds the whole alphabet. That happens first for the fence on six letters and the crown on six
  letters. See `monotone-injective-automata-on-connected-posets-are-surjective`, which stays OPEN.
- Over `Z` the window-2 census in the artifact finds, on ten connected posets, that every monotone injective rule
  fixing constants is a product of coordinate copies.
