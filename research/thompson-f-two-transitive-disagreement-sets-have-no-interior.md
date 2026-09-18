---
rg: 2
id: thompson-f-two-transitive-disagreement-sets-have-no-interior
kind: claim
title: In a 2-transitive action of Thompson's group F, no disagreement set of a pair contains an open interval
distinct_from:
  thompson-f-two-transitive-disagreement-sets-are-not-cantor: that claim excludes disagreement sets that contain no interval; this claim excludes disagreement sets that contain an interval
  thompson-f-two-transitive-disagreement-sets-are-self-similar: that claim proves that a disagreement set is never an interval and never has finitely many components; this claim excludes any interval inside it
---

Let `F` act on a set `Ω`, `|Ω| ≥ 3`, transitively on ordered pairs of distinct
points. With the disagreement set `D(ω,ω')` as defined in
`thompson-f-two-transitive-disagreement-sets-are-self-similar`, the claim is
that `D(ω,ω')` has empty interior in `[0,1]` for every pair `ω ≠ ω'`.

By the self-similar claim, `D_0` is then a compact perfect set, so the
remaining case left open by this claim is that **`D_0` has nondegenerate
interval components**. None of them is relatively open in `D_0`, so each is a
limit of other components, and every clopen piece of `D_0` contains an
interval.

This is one of the two halves of
`thompson-f-no-two-transitive-via-disagreement-set-type`. It is OPEN.

## Attempts

- 2026-09-18 (swarm-0917-w7-w7-z-break, minimal-counterexample). The set-up only.
  - If `x` is an interior point of `D(ω,ω')`, then no element of `F` that is the
    identity near `x` sends `ω` to `ω'`. The calibration in the self-similar
    claim (the order action on an orbit in `(0,1)`, where `D = [p_1,p_2]`)
    shows that interior points are natural in actions that are not
    2-transitive. There they come from an `F_U^c` fixing a point, which
    `thompson-f-two-transitive-rigid-stabilizers-fix-no-point` excludes.
  - Missing: a way to turn an interval inside `D_0` into an `F_U^c` fixing a
    point, for example by comparing `D(ω,ω')` with `D(ω,fω)` for `f` supported
    inside that interval.
