---
rg: 2
id: brin-thompson-nv-cnd-proper-modulo-triangular-subgroup
kind: claim
title: "For n >= 2 the Brin-Thompson group nV carries a cnd function proper modulo the triangular subgroup T_n"
distinct_from:
  brin-thompson-nv-cnd-proper-on-triangular-subgroup: that is the fibre half of the split (properness on T_n); this is the transversal half (properness on the coset space nV/T_n)
  brin-thompson-nv-no-cubical-action-proper-mod-triangular: that proves the cubical version of this statement is false; this asks for an arbitrary cnd function
---

**Statement.** Let `n ≥ 2` and let `T_n ≤ nV` be the triangular subgroup of
`brin-thompson-triangular-subgroup-is-undistorted`. There is a conditionally negative definite
function `ψ_1` on `nV` such that each sublevel set `{ψ_1 ≤ R}` lies in finitely many left cosets of `T_n`.

**Role.** This is the transversal prerequisite of `brin-thompson-nv-a-t-menable-via-triangular-split`.
It is necessary for the Haagerup property of `nV`, by (1) ⇒ (2) of
`haagerup-splits-as-coset-plus-subgroup-properness`.

**Forced shape.** By `brin-thompson-nv-no-cubical-action-proper-mod-triangular`, any such `ψ_1` has
`ψ_1(f^N) → ∞` and `ψ_1(f^N) = O(log^8 N)` on the Callard–Salo element, and is not a finite sum of
wall counts.

## Attempts

- 2026-09-17 (swarm-0917-w4-nv-cocycle). *Cubical transversal: dead.* The natural candidate is a
  Farley-type wall count measuring how far `g` is from triangular: walls from brick charts whose
  projections to the first `k` coordinates are not charts of `C^k`. Every commensurating action
  fails by `brin-thompson-nv-no-cubical-action-proper-mod-triangular`.
- *Weighted wall counts.* Sums `Σ_j w_j |gA_j Δ A_j|` with infinitely many commensurated sets
  escape the bounded-or-linear dichotomy. The difficulty is that `nV` acts transitively on proper
  brick charts with a fixed shape, so natural invariant weights are constant on large families and
  the series diverges. A convergent weighting would have to use the scale of the charts.
  Unexplored.
- *Relative coarse geometry.* A necessary condition is that the coset space `nV/T_n`, with the
  quotient of a word metric, has growth compatible with a Hilbert-space compression along
  `⟨f⟩`. No computation yet.
- 2026-09-17 (lane gq-nv-obstruct). *Strength, and a refutation test.* Route
  `kazhdan-finiteness-in-nv-via-cnd-transversal`. Apply `ψ_1` after the coordinate-permutation
  automorphisms of `nV`: the triangular subgroups of the `n` orders starting with each coordinate
  intersect in `V^n`. Two consequences:
  - This claim alone already makes every Kazhdan subgroup of `nV` finite (by Farley for `V^n`), with
    no fibre half. So it answers Zaremsky 2.19(a), (c) and (d) with "no". It is exactly as strong as
    a cnd function proper modulo `V^n`.
  - It is refuted by any subset of `nV` with relative property (T) that is not contained in finitely
    many left cosets of `V^n`. Such a subset would also refute the Haagerup property of `nV`.
  So this half is no easier than finiteness of Kazhdan subgroups. Constructing `ψ_1` needs a
  non-cubical cocycle that is unbounded but polylogarithmic on the Callard–Salo element; not attempted.
