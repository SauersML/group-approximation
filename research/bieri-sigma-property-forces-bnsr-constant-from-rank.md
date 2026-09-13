---
rg: 2
id: bieri-sigma-property-forces-bnsr-constant-from-rank
kind: claim
title: "A group of type F_infinity with the Bieri Sigma-property has Sigma^m(G) = Sigma^r(G) for m >= r, r the rank of Hom(G,R)"
artifacts:
  - research/artifacts/zp-properly-nested-bnsr-2026-09-13-part1.md
---

Let `G` be of type `F_∞` and `r = dim_R Hom(G,R)`. Assume `G` has the Bieri
Σ-property: `Σ^m(G)^c = conv_{≤m} Σ^1(G)^c` for every `m`. Then
`Σ^m(G) = Σ^r(G)` for all `m ≥ r`. If moreover `Σ^1(G)^c` is a finite set of
`s` classes, then `Σ^m(G) = Σ^{min(r,s)}(G)` for all `m ≥ min(r,s)`.

Here `^c` is the complement in the character sphere. The definition is
Definition 1.4 of Zaremsky, "The BNSR-invariants of the Houghton groups,
concluded", arXiv:1808.00634: "denote by conv_{≤m}S the union of convex hulls in
Σ(G) of all subsets of at most m non-antipodal elements in S". The convex hull
of a set `T` of classes is read conically: the classes of nonzero nonnegative
combinations of representatives of `T`.

Consequence for Zaremsky Problem 1.18: a group answering it affirmatively
fails the Bieri Σ-property. Two infinite-dimensional computations satisfy it.
For Thompson's `F`, `Σ^1(F)^c` is two classes and `Σ^2(F)^c = Σ^∞(F)^c` the
arc between them (Witzel–Zaremsky, arXiv:1501.06682, Theorem A). The Stein
group `F_{2,3}` has the same shape with `[λ]`, `[ρ]` and `aλ + bρ`, `a, b > 0`
(Spahn–Zaremsky, arXiv:2012.05000, Theorem 3.9). Every Houghton group has
the Bieri Σ-property (Corollary 2.7 of arXiv:1808.00634).
