---
rg: 2
id: points-of-c3-approximable-by-zero-cycles
kind: claim
title: A point of C^3 admits integral Chow forms of zero-dimensional cycles whose values on hyperplanes through the point beat any fixed multiple of height plus degree
distinct_from:
  algebraically-independent-points-approximable-by-zero-cycles: that is the statement for every s >= 3, open from s = 4; this is its case s = 3, proved from Philippon's theorem.
  philippon-zero-cycles-approximate-points-of-p3: that is the literature theorem with Philippon's distance and height; this is the Mahler-measure ratio form the Atiyah cycle inequality consumes.
---

**ESTABLISHED (unreviewed)** by [[points-of-c3-approximable-by-zero-cycles-proof]],
from [[philippon-zero-cycles-approximate-points-of-p3]].

Let `z in C^3`, put `theta~ = (1, z) in C^4`, and let `S_theta: C^3 -> C^4` be
a fixed linear parametrization of the hyperplane `{u : u . theta~ = 0}`. For a
form `F in Z[u_0..u_3]` that is a constant times a product of linear forms
`u . (1, zeta)` at points `zeta in Qbar^3`, put `b(F) = log M(F)` and
`a(F) = log M(v -> F(S_theta v))`, as in
[[algebraically-independent-points-approximable-by-zero-cycles]].

**Claim.** For every `B >= 1` and `C >= 0` there is such an `F` with

```text
a(F) + (B - 1) b(F) + C deg F  <  0.
```

`F` is the primitive Chow form of an irreducible zero-dimensional cycle over
`Q` supplied by Philippon's Theoreme 1 (JNT 81, 2000, `n = 3`, `d = 0`), with
`Delta >= max(3072^4, 3072^3 B)` and `H` large. No hypothesis on `z` is
needed. The Atiyah application uses it at points with algebraically
independent coordinates.

**Why it matters.** This is the only Diophantine input the three-variable
cycle argument needs. With the three-variable transcription of the operator
side ([[atiyah-cycle-machinery-transcribes-to-three-variables]]) it gives
[[atiyah-base-change-in-transcendence-degree-three-under-det]] through
`atiyah-transcendence-degree-three-via-philippon`.
