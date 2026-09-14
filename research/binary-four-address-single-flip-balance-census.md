---
rg: 2
id: binary-four-address-single-flip-balance-census
kind: claim
title: Over every group, 664 of the 859 unbalanced binary four-address rule classes never give an injective automaton, and the other 195 need a non-amenable table group
distinct_from:
  binary-four-address-injective-automata-have-balanced-rules: that is the full four-address statement, still open; this excludes 664 of the 859 rule classes over every group and pins each of the remaining 195 to explicit non-amenable or undecided table groups.
  three-address-binary-injective-rules-are-balanced: that settles at most three memory elements by hand; this is a computer-assisted census at exactly four, where placements that are Sidon in no group occur.
  binary-strict-pairs-need-a-memory-with-four-elements: that excludes strict pairs whose encoder and decoder memories both have at most three elements; this concerns encoders with four memory elements, whatever the decoder.
  binary-unbalanced-rules-on-sidon-memory-are-not-pre-injective: that excludes every unbalanced rule on Sidon placements; this treats every placement, including those where the memory quotients coincide.
artifacts:
  - research/artifacts/gk3-four-address-balance-census-2026-09-14.md
---

**ESTABLISHED (computer assisted)** by `binary-four-address-single-flip-census-proof`.

Let `G` be a group, `M` a subset of `G` with four elements, and `mu : {0,1}^M -> {0,1}` an unbalanced rule. Suppose
`tau(x)(g) = mu((x(g m))_(m in M))` is injective.

**Theorem.** Up to address permutations, input complement and output complement, `mu` is one of 195 explicit rule
classes. There are 859 unbalanced classes, so 664 are never realized by an injective automaton over any group.
Each surviving class:
- reads all four coordinates and satisfies `mu(0000) != mu(1111)`;
- has no invisible single-site flip in `G`;
- makes the memory group `<M>` a quotient of one of that rule's blocking table groups `G_P`, with quotient partition
  a coarsening of `P`.

**The blocking table groups.** There are 160 distinct partitions `P`, each with between 7 and 11 quotient classes.
- 131 give non-amenable free products of cyclic groups. The simplest are `Z/2 * F_2` (one involution among
  `b`, `c`, `b^-1 a`, `c^-1 a`, `c^-1 b`) and `F_2` (placements such as `{1, a, b, ab}`).
- 13 give non-amenable graph products of cyclic groups, such as `Z * (Z/2 x Z/2)`.
- 16 are undecided. Only 3 survivor classes are blocked by undecided groups alone.

The machine-readable survivor list and blocking partitions are `survivors` and `verdict` in
`experiments/gottschalk-four-address-balance/analyze3.json`.

**Where the 664 excluded classes come from.**
- 458 fail the constant test.
- 7 ignore a coordinate, and `three-address-binary-injective-rules-are-balanced` applies.
- 199 are excluded by the census:
  - 86 have an invisible single flip on every placement;
  - 113 more have, on every placement without a flip, an amenable table group or collapsing memory.

**Consequence for Gottschalk.** A two-symbol counterexample with four memory elements, if one exists, uses one of
the 195 listed rules. Its memory group is then a nonsofic quotient of a listed non-amenable table group, keeping
exactly the listed coincidences among memory quotients.

**Checks.**
- The single-flip census agrees with an independent brute-force computation on nine finite groups, 864 of 864
  verdicts.
- The table-group triage is consistency-checked through a second entry point:
  - every original relator vanishes in the recognized normal form (826 of 826);
  - the amenability flags agree;
  - all 36 finite orders are re-derived.
- No verifier lane has re-derived the census.
