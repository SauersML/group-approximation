---
rg: 2
id: semicontinuous-invariants-blind-above-rokhlin-supremum
kind: claim
title: An isomorphism invariant that is semicontinuous in the shift measure is monotone in base entropy and constant on Bernoulli shifts above the Rokhlin supremum
distinct_from:
  weak-invariants-give-no-bernoulli-rokhlin-lower-bound: that excludes weak-equivalence and orbit-relation invariants, which take one value on all nontrivial Bernoulli shifts; this excludes every semicontinuous isomorphism invariant, only above the Rokhlin supremum, and shows that below it they are monotone.
  borel-structurability-invariants-are-bernoulli-base-blind: that excludes invariants of the free Borel part, which ignore the measure; this concerns invariants of the measured action that depend semicontinuously on the measure.
  rokhlin-entropy-is-the-bernoulli-approximation-threshold: that proves the two-sided weak* approximations between Bernoulli shift models; this reads off what they force on a semicontinuous invariant.
---

Let `G` be a countably infinite group and `s = h^Rok_sup(G)`. Let `I` be an
isomorphism invariant of ergodic p.m.p. `G`-actions with values in `[−∞, ∞]`. Suppose
that for every finite set `L` the function `ν ↦ I(G ↷ (L^G, ν))` on `E_G(L^G)` is
upper semicontinuous at every Bernoulli measure `λ^G`. For `h ∈ (0, ∞)` write `I(h)`
for the value of `I` on the Bernoulli shifts of base entropy `h`, which is well
defined by `bernoulli-shifts-with-equal-base-entropy-are-isomorphic`. Then:

1. `I(h)` is non-decreasing on `(0, ∞)`;
2. `I(h)` is constant on `(s, ∞)`.

If `I` is lower semicontinuous instead, item 1 holds with "non-increasing" and item 2
holds as stated.

**Example.** Rokhlin entropy is upper semicontinuous
(`seward-approximate-bernoulli-models-and-semicontinuity`, item 2), and its value
`min(h, s)` on Bernoulli shifts is non-decreasing and constant above `s`.

**Consequence for the root.** Over a group with `s < ∞`, no semicontinuous isomorphism
invariant separates Bernoulli shifts of finite base entropies above `s`. A proof of
`bernoulli-shift-entropy-classifies-for-every-group` over such a group needs an
invariant that is not semicontinuous in the shift measure. The indicator of the
isomorphism class of `K^G` is one: when the classification holds above `s`, it is `0`
at `λ^G` and `1` along models converging to `λ^G`. With
`rokhlin-entropy-is-the-bernoulli-approximation-threshold`: on every group, a positive
proof is either a proof of INF(G) or rests on a non-semicontinuous invariant.

**ESTABLISHED 2026-09-12** by [[semicontinuous-invariants-blind-above-rokhlin-supremum-proof]].
