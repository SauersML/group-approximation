---
rg: 2
id: some-infinite-fp-torsion-free-group-has-finitely-many-classes
kind: claim
title: "Some infinite finitely presented torsion-free group has only finitely many conjugacy classes"
distinct_from:
  every-wp-group-embeds-in-fp-conjugacy-finite-group: that asks, for every finitely generated group with solvable word problem, for a finitely presented overgroup with trivial centre and finitely many conjugacy classes, torsion allowed; this asks for a single infinite torsion-free finitely presented group with finitely many conjugacy classes and no embedding condition.
  conjugacy-finite-recursive-presentation-solvable-wp: that proves a recursively presented group with finitely many conjugacy classes has solvable word problem; this asks whether an infinite torsion-free finitely presented one exists at all.
---

There is an infinite, torsion-free, finitely presented group with only
finitely many conjugacy classes.

Finitely generated examples exist: Osin's torsion-free groups with exactly
two conjugacy classes (as recorded in von Puttkamer--Wu, arXiv:1607.03790v2,
Remark (a), p. 2).  They are built as direct limits of small-cancellation
quotients.  No finitely presented example is known; the Boone--Higman region
records the same state in `every-wp-group-embeds-in-fp-conjugacy-finite-group`.

## Constraints on any witness (elementary)

Let `G` be infinite with finitely many conjugacy classes.

- Every abelian quotient is finite: its elements are images of conjugacy
  classes.  So `G` surjects onto no `Z` and is no HNN extension.
- For any isometric action of `G` on a metric space `Y`, the stable
  translation length `tau(g) = lim d(y, g^m y)/m` is conjugation invariant
  and satisfies `tau(g^m) = |m| tau(g)`.  It takes finitely many values, so
  `tau = 0` identically.  Hence `G` has no loxodromic element in any action on
  a hyperbolic space, and every infinite-order element is distorted in `G`.
  Acting on a tree, every element is elliptic; as `G` is finitely generated,
  Serre's theorem gives a global fixed point.  So `G` has property FA.

## Attempts

- **Stop a small-cancellation limit at a finite stage.**  Dies.  A finitely
  presented direct limit of a strictly increasing chain of quotients of a
  finitely generated free group equals one of its finite stages, because
  finitely many normal generators already hold at some stage.  In Osin's
  construction the finite stages are non-elementary relatively hyperbolic
  groups (not re-read here), and those have loxodromic elements, hence
  infinitely many conjugacy classes by the constraint above.
- **Higman-type embeddings of a recursively presented example.**  The
  finitely presented overgroups produced are HNN extensions and amalgams, so
  they surject onto `Z` or split nontrivially.  Dies at property FA, as
  stated above.
