---
rg: 2
id: monotone-strict-automata-ascend-along-poset-homs
kind: claim
title: A strict automaton that is monotone for a partial order on its alphabet is strict on every alphabet of order-preserving maps into it
distinct_from:
  ec-groups-share-the-nonsurjunctive-alphabet-sizes: that gives the multiples through product lifts; this gives the counts of order-preserving maps from any finite poset, which for an antichain are exactly those powers and for a chain are new sizes.
  nonsurjunctive-alphabet-sizes-are-upward-closed: that asks for every larger size; this shows a monotone strict automaton on the two-letter chain would give every size at least two, and records that such automata, and those on every chain, do not exist.
  collapse-lifts-with-unique-largest-fiber-are-surjective: that constrains lifts of an injective base; this shows every order-theoretic ascent is such a lift over the automaton induced on the connected components of the order.
  monotone-injective-chain-automata-are-translations: that is the rigidity theorem killing the chain case; this is the ascent mechanism and its reduction to collapse lifts.
artifacts:
  - experiments/monotone-poset-ascent-2026-09-17/chain_search_results.txt
---

**ESTABLISHED** by `monotone-strict-automata-ascend-along-poset-homs-proof`, from
`monotone-injective-chain-automata-are-translations` and `monotone-binary-injective-rules-are-copies`.

Let `L` be a finite poset and `ρ` an automaton on `L^G` that is *monotone*: `x <= x'` sitewise implies
`ρ(x) <= ρ(x')`. For a finite nonempty poset `P`, let `Hom(P,L)` be the set of order-preserving maps `P -> L`.

**Theorem.**
1. **Ascent.** If `ρ` is strict (injective, not surjective), then `ρ_P(f) = ρ ∘ f` is a strict automaton on
   `Hom(P,L)^G`, so `|Hom(P,L)| ∈ NS(G)` for every finite nonempty `P`.
   - `L` = the two-letter chain: `|Hom(P,L)|` is the number of down-sets of `P`, which is every `n >= 2` (chains).
   - `L` = a chain of `k` letters: the multichain counts `C(k+j-1, j)`, and their products. For example `k = 3`
     gives `10 ∉ 3N`.
   - `L` = an antichain: `|L|^c`, with `c` the number of components of `P`. These are powers, as for product lifts.
2. **Chains are dead.** No chain carries a monotone strict automaton, over any group
   (`monotone-injective-chain-automata-are-translations`). So neither case above ever fires.
3. **Covering pairs are rigid.** Replace `ρ` by a power that fixes every constant. For every covering pair `a ⋖ b`
   in `L`, the subshift `{a,b}^G` is `ρ`-invariant and `ρ` acts on it as a copy of one coordinate. More generally,
   the subshift on any interval of `L` that is a chain is invariant, and `ρ` acts on it as a copy of one coordinate.
4. **Reduction to collapse lifts.** Let `r : L -> π_0(L)` send a letter to its connected component of the
   comparability graph. Then `ρ` induces an automaton `τ̄` on `π_0(L)^G` with `r ∘ ρ = τ̄ ∘ r`. For connected `P`,
   `Hom(P,L) = ⊔_i Hom(P, L_i)`, and `ρ_P` is a letter-collapse lift of `τ̄` with fiber sizes `|Hom(P, L_i)|`.

**What this changes.**
- Order is a new mechanism for ascent. A strict automaton monotone for a partial order yields
  strict automata at every order-preserving map count, not only at the multiples. For the two-letter chain it would
  have given upward closure and descent to two at once.
- The mechanism is empty wherever the order has chains between comparable letters. Item 3 shows every chain interval
  is rigid. Item 4 shows that all remaining freedom lives in the component automaton, and there the known
  collapse-lift obstructions apply once `τ̄` is injective.
- Survivors.
  - Connected posets that are not chains, where the chain-interval rigidity does not pin the rule on incomparable
    pairs. The first is the Boolean square `2 × 2`: monotone pairs of binary layers. A strict one would give every
    square `n^2 >= 4`.
  - Disconnected posets whose component automaton `τ̄` is not injective.
