---
rg: 2
id: weakly-sofic-groups-are-surjunctive
kind: claim
title: Every weakly sofic group is surjunctive
distinct_from:
  sofic-groups-are-surjunctive: that is the Gromov--Weiss theorem for sofic groups, where the finite models are permutation groups with the Hamming metric; this asks for the same conclusion from finite models with an arbitrary bi-invariant metric, a strictly larger class by weakly-sofic-not-sofic.
  weakly-sofic-not-sofic: that separates the two approximation classes by exhibiting a weakly sofic nonsofic group; this asks whether the larger class still forces surjunctivity.
  fixed-separation-hamming-is-not-weak-soficity: that concerns whether a fixed Hamming separation can define weak soficity; this is a dynamical conclusion drawn from weak soficity.
artifacts:
  - research/artifacts/weak-soficity-surjunctivity-route-2026-09-12.md
---

**OPEN.** Let `G` be weakly sofic: for every finite `F` in `G` and every
`eps > 0` there are a finite group `H`, a conjugation-invariant length `l` on
`H`, and `phi: F -> H` with `phi(1) = 1`,
`l(phi(g)phi(h)phi(gh)^-1) <= eps` for `g, h, gh` in `F`, and
`l(phi(g)) >= c` for `g != 1` in `F`, with `c > 0` fixed. Then every injective
cellular automaton on every finite-alphabet full shift `A^G` is surjective.

## Why it is worth asking

Weak soficity is the only approximation notion in this corpus that is strictly
weaker than soficity and still supplies finite models: the Kun--Thom wreath is
weakly sofic and not sofic (`weakly-sofic-not-sofic`). A positive answer would
therefore be a surjunctivity mechanism that is **not** a permanence closure of
the sofic groups, and so is not excluded by
`sofic-permanence-closure-omits-simple-fa-nonsofic-groups`. Every other
positive mechanism on record consumes Hamming models.

It would not by itself settle `gottschalk-surjunctivity-conjecture`: whether
every group is weakly sofic is open, and Glebsky--Rivera expect not.

## Attempts

**The Gromov--Weiss count consumes an `H`-set, not a metric.** Section 1 of
the artifact isolates what the counting proof needs: a finite `H`-set `V` whose
normalized Hamming length `l_V(z) = 1 - fix(z)/|V|` is small on the
multiplicative defects and bounded below on `phi(F \ {1})`. The given length
`l` never enters the count. So the route needs `l` to force such a `V`.

**The regular action dies, maximally.** By
`regular-action-makes-weak-sofic-defects-maximal`, translation on `V = H` has
`l_V(z) = 1` for every `z != 1`. A nonzero defect therefore acquires the
largest possible Hamming defect, and Lemma 1.1 guarantees the transported identity
`sigma_V tau_V = id` at no vertex (corrected by gk-vf-positive; see Section 8.1 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`). Through the regular action, weakly
sofic data give a chart system exactly when they are already LEF data.

**The conjugation action dies for the opposite reason.** On finite simple
models with minimal class size `m(H) -> infinity`, conjugation gives
`l_V(z) >= 1 - 1/m(H)` for every `z != 1`, so separation is free and
near-multiplicativity is impossible. The two natural actions fail in opposite
directions, which is the structural obstruction.

**Simple models leave only a thin window.** By
`simple-model-weak-soficity-with-small-defect-is-lef`, on finite simple models
a defect is either trivial or has length at least `c/|H|`. So all metric
content on simple models sits in `c/|H| <= eps -> 0`, and a proof must use
defects decaying no faster than the reciprocal of the model size, or models
with a large normal subgroup carrying a small length.

**Where it stands.** The route survives only through the last case. That is
where `glebsky-rivera-w-sofic-criterion` locates the content of weak soficity,
and no argument here reaches it.
