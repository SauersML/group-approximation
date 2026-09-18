---
rg: 2
id: cubical-hosts-of-thompson-f-never-have-property-a
kind: claim
title: No CAT(0) cube complex on which a group containing Thompson's F acts with finite stabilizers has property A, so exactness of F cannot come from a proper cubical host
distinct_from:
  stein-farley-height-fixes-a-roller-boundary-point: that kills amenable-action routes through the Roller boundary of the Stein–Farley complex by a fixed point; this kills property A of every proper cubical host itself, the route to exactness that entry left undecided.
  thompson-group-f-is-exact: that is the open exactness target; this rules out one family of routes to it and says nothing about whether F is exact.
  cat0-cube-complexes-with-property-a-are-finite-dimensional: that is the general geometric input with no group; this combines it with the infinite cohomological dimension of F.
---

**ESTABLISHED** through `cubical-hosts-of-thompson-f-never-have-property-a-proof`.

Let `G` be a group containing a subgroup isomorphic to Thompson's group `F` (for example `F`, `T`, `V`, `nV`).
Let `X` be a CAT(0) cube complex, not assumed locally finite, on which `G` acts by cubical automorphisms with
finite vertex stabilizers. (Every metrically proper action has this property.)

1. `X` is infinite-dimensional.
2. `X⁽⁰⁾`, with the edge-path metric, does not have Yu's property A.

**Instances.** Farley's complexes `X_F` and `X_V` (CAT(0) and proper, Farley, IMRN 2003, as recorded in
`stein-farley-height-fixes-a-roller-boundary-point`) are proper cubical hosts, so neither has property A. For
`X_F` this can also be seen directly: a vertex of height `n` spans an `n`-cube, obtained by expanding all `n`
unit intervals.

**What this kills.** Consider the route "`F` is exact because it acts metrically properly on a CAT(0) cube
complex whose vertex set has property A". Such an action makes the orbit map a coarse embedding. The route
dies at the step "the host has property A", for every host at once. The obstruction has two parts:

- `cd F = ∞`, which forces the host to be infinite-dimensional;
- Nowak's unbounded support radius on Hamming cubes, which the gate retractions carry into the host.

Neither amenability nor exactness of `F` is decided. Any proof of exactness of `F` must use structure that no
proper cubical host sees.
