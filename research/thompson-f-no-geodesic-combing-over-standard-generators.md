---
rg: 2
id: thompson-f-no-geodesic-combing-over-standard-generators
kind: claim
title: Over every finite generating set X with x0 in X ⊆ {x0, x1, x2, ...}, Thompson's group F has no geodesic combing with the fellow traveller property, so no automatic structure over X contains a geodesic for every element
distinct_from:
  thompson-f-has-no-near-geodesic-automatic-structure: that is Hauze's theorem over the single generating set {x0, x1}, but for every additive excess c; this covers every finite subset of the standard infinite generating set, but only excess c = 0
  thompson-f-is-not-automatic: that excludes every automatic structure over every finite generating set; this excludes only languages over subsets of {x_i} that contain a geodesic representative of each element
  thompson-f-is-automatic: that is the open affirmative answer; this rules out shortlex and all other geodesic-containing automatic structures over any finite subset of the standard generators, which is where KBMAG-style searches look
artifacts:
  - experiments/thompson-f-weighted-automatic-2026-09-17/README.md
---

**ESTABLISHED** through `thompson-f-no-geodesic-combing-over-standard-generators-proof`
(an elementary lemma, plus a citation import of Horak–Stein–Taback, Theorem 4.4).

**Statement.** Let `X` be a finite subset of the standard infinite generating set
`{x0, x1, x2, ...}` of Thompson's group `F`, with `x0 ∈ X` (a subset generates `F`
exactly when it contains `x0`), and let `S = X ∪ X^-1`.

1. There is no geodesic combing of the Cayley graph `Γ(F, S)` with the synchronous
   fellow traveller property. In detail: there is no choice of one geodesic word
   `σ_g` for each `g ∈ F` and constant `K` such that `d_S(σ_g(t), σ_h(t)) <= K` for
   all `t >= 0` whenever `d_S(g, h) <= 1`. Here `σ_g(t)` is the prefix of length
   `min(t, |g|)`.
2. Consequently, no automatic structure `(W, M)` over `S` (Epstein et al.,
   *Word Processing in Groups*) has a language `W` that contains, for every
   `g ∈ F`, a geodesic word representing `g`. In particular `F` has no shortlex
   automatic structure over `S` for any ordering of `S`, and no geodesic automatic
   structure over `S`.

**Scope.**
- Over `X_1 = {x0, x1}`, part 1 is Cleary–Taback, *Seesaw words in Thompson's
  group F* (arXiv:math/0310466), Theorem 4.2. Part 2 is the `c = 0` case of
  `thompson-f-has-no-near-geodesic-automatic-structure`.
- New here: the conclusion for every finite standard subset, for example
  `X_n = {x0, ..., xn}` or `{x0, x_7, x_19}`. The literature read on 2026-09-17
  has no geodesic-combing or regular-geodesic-language result for these sets.
  Cleary–Elder–Taback (arXiv:math/0410616) and Hauze work over `{x0, x1}` only.
- The additive-excess case `c > 0` over `X ≠ X_1` stays open. The multiplicative
  case, over any generating set, is Zaremsky Problem 2.2 itself.

**Why it matters for the target.** Word-length sets and the heuristics used
to search for automatic structures, such as KBMAG shortlex over `x0, x1, x2, ...`,
live on these generating sets. An automatic structure over any of them must omit
the geodesics of some elements. Structures with uniqueness must therefore contain
words with positive excess over geodesic length.

**Computational companion** (experiments README). This is an exact SAT
certificate that the ball `B_5` of `Γ(F, X_2)` (2067 elements) has no geodesic
combing with fellow traveller constant `<= 3`. Over `X_1`, `B_6` (1381 elements)
has none with constant `<= 5`. The minimal constant on these balls grows with the
radius, as the theorem predicts.
