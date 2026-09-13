---
rg: 2
id: brin-thompson-nekrashevych-groups-have-simple-alternating-core
kind: claim
title: Every higher-dimensional Rover--Nekrashevych group nV_d(H) has a simple normal subgroup A contained in every non-trivial normal subgroup, by Nekrashevych's Theorem 1.1
distinct_from:
  rover-nekrashevych-finite-presentation-criteria: that records finite presentation and simplicity of [V_d(H),V_d(H)] in dimension one; this gives the simple minimal normal subgroup in every dimension n, with no finite-presentation conclusion.
  brin-thompson-nekrashevych-wp-reduces-to-self-similar-group: that bounds the word problem of nV_d(H); this identifies its minimal normal subgroup.
---

**ESTABLISHED.**

**Setting.** `nV_d(H)` is as in
`brin-thompson-nekrashevych-wp-reduces-to-self-similar-group`, acting on the
Cantor space `(X^ω)^n`, for any self-similar `H ≤ Aut(T_d)`.

**Statement.** Let `G_H` be the groupoid of germs of the action of `nV_d(H)`
on `(X^ω)^n`. Then:
1. `G_H` is a minimal groupoid of germs, and its topological full group is
   `nV_d(H)`;
2. the alternating group `A(G_H) ≤ nV_d(H)` of Nekrashevych is simple, and it
   is contained in every non-trivial normal subgroup of `nV_d(H)`.

**Source** (arXiv:1511.08241v2, V. Nekrashevych, *Simple groups of dynamical
origin*; text extracted from the arXiv PDF on 2026-09-13):
- Theorem 1.1: "Let G be a minimal groupoid of germs. Then A(G) is simple, and
  is contained in every non-trivial normal subgroup of the topological full
  group of G."
- Standing assumptions: all groupoids are étale and "the unit space G(0) is
  homeomorphic to the Cantor set".
- Definition 2.3 defines the full group as the set of bisections `F` with
  `s(F) = r(F) = G(0)`. The paper adds: "if G is a groupoid of germs, then our
  definition agrees with the H. Matui's definition", i.e. a homeomorphism group
  of `G(0)`.
- "A groupoid G is said to be minimal if all its orbits are dense in G(0)."

**Scope.**
- No finite generation or finite presentation of `A(G_H)` is claimed. The
  source's Theorem 1.2 needs expansivity, which fails for infinite `H`.
- No claim is made that a given subgroup of `nV_d(H)` lies in `A(G_H)`.
- For trivial `H` this recovers a simple minimal normal subgroup of Brin's
  `nV`, which is simple itself.

The proof is `brin-thompson-nekrashevych-alternating-core-proof`.
