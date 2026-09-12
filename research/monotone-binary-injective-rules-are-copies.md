---
rg: 2
id: monotone-binary-injective-rules-are-copies
kind: claim
title: Over every group, an injective binary automaton with a monotone rule is a copy of one coordinate
distinct_from:
  three-address-binary-injective-rules-are-balanced: that excludes every unbalanced binary rule on three memory elements through flips glued by an involution; this excludes monotone rules on any number of memory elements through constant backgrounds alone.
artifacts:
  - research/artifacts/unbalanced-design-memory-collisions-2026-09-12.md
---

**ESTABLISHED 2026-09-12** by `monotone-binary-injective-rules-are-copies-proof`.

Let `G` be any group and `tau` an injective automaton on `{0,1}^G` whose memory is a finite set `M`.
- If its rule is nondecreasing in every coordinate, then `mu = x_t` for a single `t` in `M`.
- If its rule is nonincreasing in every coordinate, then `mu = 1 - x_t`.

In particular, thresholds, biased majorities and negation-free AND/OR circuits never give injective
automata unless they are copies, so they never give Gottschalk counterexamples.

**Why.** Constant backgrounds must be sensitive somewhere: for each background `c` some address `m`
has `mu(c at M \ m, 1 - c at m) != mu(c at M)`, or a one-site perturbation of the constant
configuration is invisible. Monotonicity then sandwiches `x_t <= mu <= x_t'`, which forces `t = t'`.
