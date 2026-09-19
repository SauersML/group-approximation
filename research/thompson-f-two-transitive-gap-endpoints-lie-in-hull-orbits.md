---
rg: 2
id: thompson-f-two-transitive-gap-endpoints-lie-in-hull-orbits
kind: claim
title: In a 2-transitive action of Thompson's group F, every left gap endpoint of a disagreement set lies in the orbit of the upper hull endpoints and every right gap endpoint in the orbit of the lower ones
distinct_from:
  thompson-f-two-transitive-hull-endpoints-are-rational: that claim locates the two extreme points of a disagreement set in single rational orbits; this claim locates every gap endpoint, which is a statement about the whole set
  thompson-f-two-transitive-disagreement-sets-are-self-similar: that claim gives splicing and self-similarity of the set; this claim combines splicing with the hull orbits to pin down the gap endpoints
---

Let `F` act on a set `Ω`, `|Ω| ≥ 3`, transitively on ordered pairs of
distinct points. Use `D(ω,ω')` and `D_0` as in
`thompson-f-two-transitive-disagreement-sets-are-self-similar`, and the hull
endpoints `ξ ≤ η` and the rational orbits `Θ^+ ∋ ξ(ω,ω')`,
`Θ^- ∋ η(ω,ω')` as in `thompson-f-two-transitive-hull-endpoints-are-rational`.
A **gap** of a closed set `D ⊆ [0,1]` is an open interval `(a,b)` with
`a, b ∈ D` and `(a,b) ∩ D = ∅`.

1. If `(a,b)` is a gap of `D(ω,ω')`, then `a ∈ Θ^-` and `b ∈ Θ^+`. In
   particular every gap endpoint of every disagreement set is rational.
2. More precisely there is `α ∈ Ω ∖ {ω,ω'}` with `a = η(ω,α)`,
   `b = ξ(α,ω')`, `D(ω,α) = D(ω,ω') ∩ [0,a]` and
   `D(α,ω') = D(ω,ω') ∩ [b,1]`.
3. (Cantor case.) If `D_0` has empty interior, then `D_0 ∩ Θ^-` and
   `D_0 ∩ Θ^+` are both dense in `D_0`. So the rational points of `D_0` are
   dense in `D_0`, although `D_0` is uncountable.

This is a necessary condition on the shape of `D_0` in both cases of the
dichotomy of `thompson-f-no-two-transitive-via-disagreement-set-type`. It is
used in `quaternary-cantor-set-passes-disagreement-shape-tests`, which shows
that the necessary conditions on the orbit `F·D_0` known so far, this one
included, are all met by an explicit Cantor set.

Scope: proved here on 2026-09-19 by swarm agent
`swarm-0917-w15-w15-z-last1`. The proof is three lines from the two
prerequisites. There is no independent review, and no novelty is claimed.

**Proof:** `thompson-f-two-transitive-gap-endpoints-lie-in-hull-orbits-proof`.
