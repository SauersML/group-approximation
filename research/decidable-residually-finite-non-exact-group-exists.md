---
rg: 2
id: decidable-residually-finite-non-exact-group-exists
kind: claim
title: Osajda's recursive residually finite non-exact group has solvable word problem, so some decidable simple Kazhdan group is not exact
distinct_from:
  recursive-residually-finite-non-exact-groups-exist: that says the group is recursively presented, which only makes its word problem recursively enumerable; this says the word problem is solvable, by reducing each word to the finitely presented residually finite stage whose ball radius is the word length.
  residually-finite-non-exact-groups-exist: that is Osajda's existence theorem with no algorithmic content; this places one of his groups on the input side of Boone--Higman.
  universal-recursive-lef-host-is-not-exact: that shows the one universal LEF host is non-exact, and that host must contain every recursively presented LEF group, so nothing controls its word problem; this gives a non-exact simple Kazhdan LEF group with solvable word problem.
  some-simple-kazhdan-lef-groups-are-not-exact: that gives a non-exact simple Kazhdan LEF host with no control of its word problem; this controls it.
artifacts:
  - research/artifacts/exactness-boone-higman-separator-2026-09-17.md
  - research/artifacts/sk-free-1-exactness-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Route: `decidable-residually-finite-non-exact-group-proof`.

## Theorem

1. There is a finitely generated, residually finite group `G` that is not exact (it has no property A) and has **solvable word problem**. Osajda's graphical small cancellation group built from a recursive input sequence (`recursive-residually-finite-non-exact-groups-exist`) is one.
2. There is an infinite, finitely generated, simple group with property (T) that is LEF, has solvable word problem, and is **not exact**.

## The key reduction

Osajda's construction supplies:
- finitely presented residually finite stages `G_n`, with quotient maps `G_n → G`;
- finite quotients `φ_n` of `G_n` that are nontrivial on every nontrivial element of the radius-`n` ball of `G_n` (his condition (C)), and that are compatible with the quotient maps (his condition (D)), so they factor through `G`.

Hence, for every word `w` of length at most `n`,

    w = 1 in G   iff   w = 1 in G_n.

The presentation of `G_n` is computable from `n`, and McKinsey's algorithm decides the word problem of `G_n` uniformly. So the word problem of `G` is solvable.

Item 2 follows from `lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts`, since residually finite groups are LEF. Property A passes to subgroups (Willett, Lemma at l.1607 of arXiv:math/0612492, quoted in the artifact), so the host is non-exact.

## Why it matters

`G` is a Boone--Higman input that is residually finite, LEF, sofic and hyperlinear, yet not exact. It passes every approximation filter of `hereditary-approximation-disproofs-of-boone-higman`, but it fails the operator-algebraic one. `exactness-separates-boone-higman-iff-fp-simple-groups-exact` uses it.
