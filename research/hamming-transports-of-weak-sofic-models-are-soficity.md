---
rg: 2
id: hamming-transports-of-weak-sofic-models-are-soficity
kind: claim
title: A group admits uniform Hamming transports of its weakly sofic models exactly when it is sofic
invalidates: [weakly-sofic-surjunctivity-via-hamming-transport]
distinct_from:
  permutation-lengths-are-convex-hulls-of-coset-lengths: that describes which Hamming lengths a finite group's actions can realize; this says that realizing small defects and fixed separation for every finite set is the same as soficity, so the linear program never reaches a nonsofic group.
  regular-action-makes-weak-sofic-defects-maximal: that is the failure of one particular action; this covers every finite action and every mixture at once.
  weakly-sofic-not-sofic: that separates the two approximation classes; this uses the separation to kill the chart-transport method on nonsofic weakly sofic groups.
artifacts:
  - research/artifacts/weak-sofic-hamming-transport-is-soficity-2026-09-12.md
---

**ESTABLISHED.** Say `G` admits *uniform Hamming transports of weakly sofic
models* if there is `c' > 0` such that for every finite `F` in `G` and every
`delta > 0` there are a weakly sofic approximation `(H, l, phi)` on `F` and a
finite `H`-set `V` with normalized Hamming length `l_V(z) = 1 - fix(z)/|V|`
satisfying

```text
l_V( phi(a) phi(b) phi(ab)^-1 ) <= delta     for a, b, ab in F,
l_V( phi(g) )                   >= c'        for g != 1 in F.
```

Then `G` admits uniform Hamming transports if and only if `G` is sofic.

**Consequences.**
- The Kun--Thom wreath is weakly sofic and not sofic (`weakly-sofic-not-sofic`),
  so it admits no uniform Hamming transport: some finite set and some
  `delta_0 > 0` defeat every weakly sofic model and every finite action.
- Counting on the `H/N`-set of a normal subgroup, with defects absorbed in the
  fibres, is the case `l_V = [z not in N]`. It needs defects in `N` and
  separation outside `N`, which is an exact local embedding into `H/N`.
- The linear program of `permutation-lengths-are-convex-hulls-of-coset-lengths`
  with vanishing defect bound and fixed separation is infeasible, for some
  finite set, on every nonsofic group.

So no argument that supplies Gromov--Weiss charts for every finite set, from
weakly sofic models through finite actions, can prove
`weakly-sofic-groups-are-surjunctive` beyond the sofic groups.

Proof: Sections 1--2 of the artifact, route
`hamming-transports-are-soficity-proof`.
