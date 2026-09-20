---
rg: 2
id: monotone-injective-chain-automata-are-translations
kind: claim
title: Over every group, an injective automaton on a linearly ordered alphabet whose rule is monotone is a copy of one coordinate
distinct_from:
  monotone-binary-injective-rules-are-copies: that is the two-letter case, proved by sandwiching the rule between two coordinates on constant backgrounds; this is every finite chain, where the rule is not sandwiched by constants alone and the proof needs charge noncreation at an interior background level.
  finite-injective-charge-noncreation-forces-surjectivity: that is the tool used at the interior level; this is a rigidity theorem for a whole class of rules.
  monotone-strict-automata-ascend-along-poset-homs: that shows what a strict monotone automaton on a poset alphabet would give; this kills the chain case of it.
artifacts:
  - experiments/monotone-poset-ascent-2026-09-17/chain_monotone_search.py
---

**ESTABLISHED** by `monotone-injective-chain-automata-are-translations-proof`, from
`monotone-binary-injective-rules-are-copies` and `finite-injective-charge-noncreation-forces-surjectivity`.

**Theorem.** Let `G` be any group, `k >= 1`, and `L = {0 < 1 < ... < k-1}` a finite chain. Let `ρ` be an injective
cellular automaton on `L^G` whose local rule is nondecreasing in every address (equivalently `x <= x'` sitewise
implies `ρ(x) <= ρ(x')`). Then there is `t ∈ G` with `ρ(x)(h) = x(ht)` for all `x` and `h`: `ρ` is a copy of one
coordinate, hence bijective.

Nonincreasing rules reduce to this case by composing with the order reversal `c -> k-1-c`, which gives
`ρ(x)(h) = k-1-x(ht)`.

**Consequences.**
- Put any linear order on an alphabet of any size. No strict automaton has a rule that is monotone for that order.
  So thresholds, max-min (lattice polynomial) rules, ranked or sorting filters and every other monotone rule over a
  chain never give a Gottschalk counterexample, over any group and at any alphabet size.
- The chain case of the ascent `monotone-strict-automata-ascend-along-poset-homs` is empty. A strict monotone
  automaton on the two-letter chain would have given every size `n >= 2`, and one on a longer chain every
  multichain count. None exists.
- Over `Z` the exhaustive search in the artifact confirms it for chains of 3 and 4 letters with windows of 2, and
  for 3 letters with windows of 3. Every monotone injective rule found is a copy of one coordinate.
