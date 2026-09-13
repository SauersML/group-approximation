---
rg: 2
id: f-infinity-finite-cd-groups-have-contractible-rips
kind: claim
title: Every group of type F_infinity with finite cohomological dimension has a contractible Rips complex
distinct_from:
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for the single group Z^n; this asserts a contractible Rips complex for every group of type F_infinity with finite cd
  hyperbolic-rips-complex-models-proper-actions: that is the Meintrup–Schick model for hyperbolic groups; this is the universal statement over the class F_infinity plus finite cd
  every-type-f-group-has-a-contractible-rips-complex: that is the affirmative answer to Problem 4.7 for groups of type F; this is the affirmative answer to Problem 4.6 for the larger class F_infinity plus finite cd, equivalent to that claim together with the affirmative answer to Problem 1.21
---

For every group `G` of type `F_∞` with `cd G < ∞` there are a finite
symmetric generating set `S` and a scale `r ≥ 1` such that the closed Rips
complex `R_r(G,S)` is contractible.

The affirmative answer to Zaremsky Problem 4.6
(`zaremsky-4-06-f-infinity-finite-cd-contractible-rips`). By
`contractible-rips-complex-gives-finite-classifying-space` it implies that every
such `G` is of type F. Every finitely presented group of type FP is of type
`F_∞` with finite cd, so it would also answer, for finitely presented groups,
Bass's question whether type FP implies type FF.

## Attempts

- **Brown's criterion gives only essential contractibility.** For `G` of type
  `F_∞` the filtration `R_1 ⊆ R_2 ⊆ ⋯` of the full simplex on `G` is
  essentially contractible: for all `k` and `r` there is `r'` with
  `π_k(R_r) → π_k(R_{r'})` zero (K. S. Brown, *Finiteness properties of groups*,
  JPAA 44 (1987)). Where it stops: no single level is known to be contractible,
  or even `(n−1)`-connected for `n ≥ 3` (Problem 4.4). Finite cd does not help at
  a fixed level. A contractible level makes `R_r/G` a finite `K(G,1)`
  (`contractible-rips-complex-gives-finite-classifying-space`), which forces the
  Wall finiteness obstruction `σ(G) ∈ K̃_0(ZG)` to vanish, so any proof must also
  settle Problem 1.21. In a level acyclic below its top dimension, `σ(G)` is the
  class of the top homology (`top-homology-of-free-complex-carries-wall-obstruction`).
- **Known classes (all already of type F).** Contractible Rips complexes exist
  for hyperbolic groups (`hyperbolic-rips-complex-models-proper-actions`), `Z^n`
  (`rips-complexes-of-integer-lattices-are-contractible`), and by Li–Sánchez
  Saldaña (arXiv:2608.24279) for RAAGs on triangle-free graphs with standard
  generators (Theorem 1.5), `Z^n × F` with `F` finite (Theorem 1.6), and
  amalgams, HNN extensions over finite groups and free products of type `ℝ`
  marked groups (Theorems 1.3, 1.4, Corollary 3.1). Finite direct products of
  groups with contractible Rips complexes have them too
  (`contractible-rips-groups-closed-under-direct-products`). The Problem 4.7 lane
  adds `torsion-free-asymptotically-cat0-groups-have-contractible-rips`,
  `coarsely-injective-groups-have-contractible-rips-complexes`,
  `torsion-free-hhg-subgroups-have-contractible-rips-complexes` and
  `helly-groups-have-contractible-rips-complexes`. As of 73e31d2c69 the last three
  are unreviewed. So this claim holds for every group of type `F_∞` with finite cd
  in those classes. None of these classes reaches a group known only to be `F_∞`
  with finite cd.
- **Equivalence, wired.** `f-infinity-fcd-contractible-rips-from-1-21-and-4-07`
  proves this claim from `f-infinity-groups-of-finite-cd-are-of-type-f` (Problem
  1.21, yes) and `every-type-f-group-has-a-contractible-rips-complex` (Problem 4.7,
  yes). `f-infinity-fcd-type-f-from-contractible-rips` and
  `type-f-contractible-rips-from-f-infinity-fcd-rips` derive both of those from
  this claim. For `G` with `K̃_0(ZG) = 0`, `F_∞` plus finite cd already gives type F
  (`f-infinity-finite-cd-group-with-zero-reduced-k0-is-type-f`, including the
  Farrell–Jones classes). For such `G` the question is exactly Problem 4.7. Where
  it stops: both conjuncts are open.
