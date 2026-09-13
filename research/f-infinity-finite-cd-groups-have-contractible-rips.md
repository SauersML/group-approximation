---
rg: 2
id: f-infinity-finite-cd-groups-have-contractible-rips
kind: claim
title: Every group of type F_infinity with finite cohomological dimension has a contractible Rips complex
distinct_from:
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for the single group Z^n; this asserts a contractible Rips complex for every group of type F_infinity with finite cd
  hyperbolic-rips-complex-models-proper-actions: that is the Meintrup–Schick model for hyperbolic groups; this is the universal statement over the class F_infinity plus finite cd
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
  settle Problem 1.21.
- **Known classes (all already of type F).** Contractible Rips complexes exist
  for hyperbolic groups (`hyperbolic-rips-complex-models-proper-actions`), `Z^n`
  (`rips-complexes-of-integer-lattices-are-contractible`), and by Li–Sánchez
  Saldaña (arXiv:2608.24279) for RAAGs on triangle-free graphs with standard
  generators (Theorem 1.5), `Z^n × F` with `F` finite (Theorem 1.6), and
  amalgams, HNN extensions over finite groups and free products of type `ℝ`
  marked groups (Theorems 1.3, 1.4, Corollary 3.1). None of these reaches a
  group known only to be `F_∞` with finite cd.
- **Reduction.** This claim is equivalent to the conjunction of (1.21) every
  `F_∞` group with finite cd is of type F, and (4.7) every type F group has a
  contractible Rips complex. The routes into this claim and out of it are wired
  when the Problem 1.21 and 4.7 answer claims exist.
