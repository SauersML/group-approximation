---
rg: 2
id: quaternary-cantor-set-passes-disagreement-shape-tests
kind: claim
title: The F-orbit of the base-4 Cantor set with digits 0 and 1 satisfies every known shape condition on the disagreement sets of a 2-transitive action of Thompson's group F
distinct_from:
  thompson-f-two-transitive-disagreement-sets-are-not-cantor: that claim asserts that disagreement sets cannot be Cantor sets; this claim is a calibration showing that no contradiction follows from the shape conditions on the orbit of D_0 alone, so a proof of that claim needs data from the abstract set
  thompson-f-two-transitive-disagreement-sets-are-self-similar: that claim derives shape conditions from a 2-transitive action; this claim builds an explicit Cantor set, with no action, that satisfies them
  thompson-f-two-transitive-gap-endpoints-lie-in-hull-orbits: that claim derives the gap endpoint condition; this claim checks it, with the other conditions, on an explicit example
---

Let `F` be Thompson's group, acting on `[0,1]` by piecewise linear
homeomorphisms with finitely many dyadic breakpoints and slopes in `2^Z`. A
**dyadic affine map** is `ψ(x) = 2^k x + d` with `k ∈ Z`, `d ∈ Z[1/2]`. Put

`C = { Σ_{i≥1} d_i 4^{-i} : d_i ∈ {0,1} } ⊂ [0,1/3]`,   `K = 1/2 + C/4 ⊂ [1/2, 7/12]`.

So `C` is the set of points of `[0,1/3]` whose binary digits in odd places are
`0`, the example suggested in the 2026-09-18 attempt on
`thompson-f-two-transitive-disagreement-sets-are-not-cantor`. Let
`𝒦 = F·K = { fK : f ∈ F }`, `Θ^+ = Z[1/2] ∩ (0,1)` (the dyadic orbit) and
`Θ^- = F·(1/3)`.

1. (Description.) `𝒦` is the set of finite unions of pairwise disjoint sets
   `ψ(K) ⊂ (0,1)` with `ψ` dyadic affine.
2. (Pieces and unions.) Every nonempty relatively clopen subset of a member of
   `𝒦` is in `𝒦`. The union of two disjoint members of `𝒦` is in `𝒦`.
3. (Topology.) Every member of `𝒦` is a Cantor set in `(0,1)`. In particular
   it is compact, perfect and not connected, and it has empty interior.
4. (Endpoints.) For `D ∈ 𝒦`: `min D ∈ Θ^+`, `max D ∈ Θ^-`, and
   `min D < max D`. For every gap `(a,b)` of `D`, `a ∈ Θ^-` and `b ∈ Θ^+`.
   Both `D ∩ Θ^-` and `D ∩ Θ^+` are dense in `D`.
5. (Swap-like elements.) For every `D ∈ 𝒦` there is `f ∈ F` with `fD = D`
   that fixes `min D` and `max D` and has both one-sided slopes equal to `1/4`
   at each of them. So `f` is the identity near neither point.

**The shape conditions 𝔖.** For an `F`-orbit `𝒟` of compact subsets of
`(0,1)` and two `F`-orbits `Θ^±` of rational points, consider:

- (S1) members of `𝒟` are perfect and not connected (items 5 and 6 of
  `thompson-f-two-transitive-disagreement-sets-are-self-similar`);
- (S2) nonempty clopen pieces of members are members (its item 4);
- (S3) disjoint members have union a member. This is stronger than what Step 8
  of its proof produces, namely one such union;
- (S4) `min D ∈ Θ^+`, `max D ∈ Θ^-`, `min D < max D` (its item 7, with
  `thompson-f-two-transitive-hull-endpoints-are-rational` and
  `thompson-f-two-transitive-hull-endpoints-are-separated`);
- (S5) the gap endpoint and density conditions of
  `thompson-f-two-transitive-gap-endpoints-lie-in-hull-orbits`;
- (S6) every member `D` is stabilized by an element fixing `min D` and
  `max D` that is the identity near neither and has slope `≠ 1` at each
  non-dyadic one. For `D = D(ω,ω')` this is what a swap of `ω, ω'` gives
  (`thompson-f-two-transitive-hull-endpoints-are-rational`).

Items 1–5 say that `(𝒦, Θ^+, Θ^-)` satisfies (S1)–(S6) and empty interior.

**What this kills.** No contradiction follows from (S1)–(S6) plus empty
interior, because `(𝒦, Θ^+, Θ^-)` is a model of them. So no proof of
`thompson-f-two-transitive-disagreement-sets-are-not-cantor` can use only
properties of the orbit `F·D_0` and of the endpoint orbits. A proof must use
data tied to the abstract set `Ω`. The candidates are:

- how disagreement sets of different pairs overlap, for example
  `D(ω,·)` restricted to the `F_ω`-orbit, or the triple rule in item 1 of
  the self-similar claim;
- colourings with three or more colours;
- germs of the point stabilizer, as in the germ formula
  `D(ω,aω) = { x : a^{-1}` agrees near `x` with no element of `F_ω }`.

The model says nothing about whether any action realizes `𝒦`. It does not show
that the Cantor case occurs.

Scope: proved here on 2026-09-19 by swarm agent `swarm-0917-w15-w15-z-last1`.
It uses only standard facts about `F` (Cannon–Floyd–Parry, *Introductory notes
on Richard Thompson's groups*, Enseign. Math. 42 (1996), Lemma 4.2). There is
no independent review, and no novelty is claimed.

**Proof:** `quaternary-cantor-set-passes-disagreement-shape-tests-proof`.
