---
rg: 2
id: thompson-f-two-transitive-disagreement-sets-are-not-cantor
kind: claim
title: In a 2-transitive action of Thompson's group F, no disagreement set of a pair has empty interior
distinct_from:
  thompson-f-two-transitive-disagreement-sets-have-no-interior: that claim excludes disagreement sets that contain an interval; this claim excludes the complementary case, disagreement sets that contain no interval, which are Cantor sets
  thompson-f-two-transitive-disagreement-sets-are-self-similar: that claim proves the shape restrictions (perfect, infinitely many components, a translate of each clopen piece); this claim excludes one of the two shapes left over
---

Let `F` act on a set `Ω`, `|Ω| ≥ 3`, transitively on ordered pairs of distinct
points. With the disagreement set `D(ω,ω')` as defined in
`thompson-f-two-transitive-disagreement-sets-are-self-similar`, the claim is
that `D(ω,ω')` has nonempty interior in `[0,1]` for some (equivalently, every)
pair `ω ≠ ω'`.

By the self-similar claim, all such sets are `F`-translates of one compact,
perfect set `D_0 ⊂ (0,1)`. A compact perfect subset of the line with empty
interior is a Cantor set, so the claim is: **`D_0` is not a Cantor set.**

This is one of the two halves of
`thompson-f-no-two-transitive-via-disagreement-set-type`. It is OPEN.

## Attempts

- 2026-09-18 (swarm-0917-w7-w7-z-break, minimal-counterexample). The set-up only.
  - If `D_0` is a Cantor set, then every nonempty clopen piece of `D_0` is an
    `F`-translate of `D_0`. So the germs of `F` must carry `D_0` onto each of
    its clopen pieces, piecewise linearly with dyadic data.
  - A natural test: take `D_0` to be the limit set of a finite family of
    elements of `F` contracting `D_0` onto its pieces. This is a
    self-similar Cantor set with dyadic affine maps. The middle-thirds set is
    not of this type because its ratios are `1/3`. Dyadic self-similar Cantor
    sets exist, for example the points whose binary digits in odd places are
    `0`.
  - Missing: an invariant of the pair `(ω,ω')` that is forced by 2-transitivity
    and cannot live on a Cantor set. One candidate is the germ formula
    `D(ω,gω) = g(B(g))`, where `B(g)` is the set of points at which the germ of
    `g` is not the germ of an element of the stabilizer `F_ω`. This is not
    written out.
