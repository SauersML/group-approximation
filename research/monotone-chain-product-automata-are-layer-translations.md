---
rg: 2
id: monotone-chain-product-automata-are-layer-translations
kind: claim
title: Over every group, a monotone injective automaton on a product of chains translates each layer rigidly, so it is bijective
distinct_from:
  monotone-injective-chain-automata-are-translations: that is one chain, where the automaton is a copy of one coordinate; this is a product of chains, where each layer is a copy of its own coordinate and the layers may use different translations, so the automaton need not be a copy of one coordinate.
  monotone-binary-injective-rules-are-copies: that is the two-letter chain; this includes every Boolean lattice, where each binary layer is such a copy.
  monotone-strict-automata-ascend-along-poset-homs: that is the ascent mechanism, whose first recorded survivor is the Boolean square; this kills that survivor and every product of chains.
artifacts:
  - experiments/monotone-lattice-glue-2026-09-17/lattice_search_results.txt
---

**ESTABLISHED** by `monotone-chain-product-automata-are-layer-translations-proof`, from
`monotone-injective-chain-automata-are-translations`.

**Theorem.** Let `G` be any group, and let `L = C_1 x ... x C_m` be a finite product of finite chains, with the
product order. Let `ρ` be an injective cellular automaton on `L^G` that is monotone: `x <= x'` sitewise implies
`ρ(x) <= ρ(x')`.
1. There are `N >= 1` and `t_1, ..., t_m ∈ G` with `ρ^N(x)(h) = (π_i x(h t_i))_{i=1..m}` for all `x` and `h`, where
   `π_i : L -> C_i` is the projection. Any `N` for which `ρ^N` fixes every constant works, and then each layer of
   `ρ^N` is a translation.
2. So `ρ^N` is bijective, and `ρ` is bijective.

**Consequences.**
- The Boolean square `2 x 2` carries no strict monotone automaton, over any group. It was the first survivor recorded
  under `monotone-strict-automata-ascend-along-poset-homs`, and a strict one would have given every square
  `n^2 >= 4` as a nonsurjunctive size.
- The same holds for every Boolean lattice `2^m`, every grid `[k_1] x ... x [k_m]`, and every divisor lattice of an
  integer, which is a product of chains.
- The layers may use different translations: `(x_1, x_2) -> (x_1 ∘ λ_s, x_2 ∘ λ_u)` with `s != u` is monotone and
  bijective. So the product case is not a copy of one coordinate, and a rigidity proof for general posets must allow
  one translation per direct factor.
- Where the class dies. After a power fixing constants, each layer is pinned between its values on the two extreme
  backgrounds of the other layers (all bottoms, all tops). The chain theorem makes both of them translations, and the
  sandwich forces the two translations to coincide.
