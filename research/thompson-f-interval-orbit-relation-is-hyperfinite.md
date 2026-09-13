---
rg: 2
id: thompson-f-interval-orbit-relation-is-hyperfinite
kind: claim
title: The orbit equivalence relation of Thompson's group F on (0,1) is hyperfinite for every quasi-invariant measure
distinct_from:
  thompson-f-end-rigid-schreier-graphs-are-amenable: that gives Følner sets in Schreier graphs of F-sets; this is measured amenability of the orbit equivalence relation on the interval, a statement about orbits rather than graphs.
  thompson-f-is-not-strongly-amenable: that is about proximal topological actions; this is about the measured orbit structure of the natural action.
artifacts:
  - research/artifacts/zp-thompson-f-nonamenability-certificates-2026-09-13.md
---

**ESTABLISHED.** Let `Aff` be the group of maps `t ↦ 2^k t + d` of `R` (`k ∈ Z`,
`d ∈ Z[1/2]`), which is solvable, and let `R_F = {(t, f(t)) : t ∈ (0,1), f ∈ F}`.

1. `R_F = R_Aff ∩ (0,1)^2`: two points of `(0,1)` are in one `F`-orbit iff they differ by a
   dyadic affine map.
2. For every `F`-quasi-invariant σ-finite Borel measure `μ` on `(0,1)`, the measured
   equivalence relation `(R_F, μ)` is hyperfinite, equivalently amenable.

**Consequence.** No argument of the form "some measured orbit relation of `F` on the interval
is non-amenable" can prove non-amenability of `F`; see
`thompson-f-interval-orbit-relation-is-nonamenable`, which this claim refutes. That is the
mechanism of Monod's non-amenability theorem for piecewise projective groups (arXiv:1209.5229,
Theorem 1.1, through Carrière–Ghys and non-discrete free subgroups of `PSL_2(A)`). For `F` the
local maps form the solvable group `Aff`, and the mechanism is unavailable.

**Scope.** It uses Zimmer (1977: non-singular actions of amenable groups are amenable) and
Connes–Feldman–Weiss (1981: amenable relations are hyperfinite), cited as standard and not
re-read. Very likely folklore; no novelty is claimed.

Proof route: `thompson-f-interval-orbit-relation-is-hyperfinite-proof`.
