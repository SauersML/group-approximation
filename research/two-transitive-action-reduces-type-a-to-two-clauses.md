---
rg: 2
id: two-transitive-action-reduces-type-a-to-two-clauses
kind: claim
title: For a faithful 2-transitive action the type (A) conditions collapse to finite presentation of the group and finite generation of one point stabilizer
distinct_from:
  type-a-action-gives-boone-higman-for-subgroups: that is the imported corollary saying what a type (A) action buys; this is an elementary reduction of the four type (A) clauses to two under an extra transitivity hypothesis, and buys nothing on its own.
  relative-automorphism-action-is-highly-transitive: that is an imported statement about one specific action being highly transitive with finitely generated stabilizers; this is the general observation that high transitivity discharges the pair-orbit clause, and explains why that route has only one open leaf.
  fiber-product-conjugation-action-lemma: that computes the pair orbits of a two-sided translation action and finds conjugacy classes, which are generally many; this observes that a 2-transitive action has exactly one pair orbit, which is the opposite extreme and needs no computation.
  simple-core-bi-index-counts-coset-action-pair-orbits: that counts pair orbits of a coset action by double cosets, so its pair-orbit clause is a real hypothesis; this is the case where the count is 1 for free.
artifacts:
  - research/artifacts/boone-higman-fiber-product-and-shift-compiler-2026-08-24.md
---

Let `G` act faithfully and 2-transitively on a set `S` with `|S| >= 2`.
Then the action is of type (A) if and only if

* `G` is finitely presented, and
* `Stab_G(s)` is finitely generated for one, equivalently every, `s in S`.

## Proof

Clause 1 of type (A) is faithfulness, hypothesized.  For clause 4:
2-transitivity means `G` is transitive on ordered pairs of distinct elements
of `S`, and every two-element subset is the underlying set of such a pair, so
there is exactly one orbit of two-element subsets.  For clause 3, transitivity
makes all point stabilizers conjugate, hence simultaneously finitely
generated or not.  Clause 2 is unchanged.  `∎`

## Why the graph carries it

It says where the difficulty of a type (A) construction actually lives.  The
pair-orbit clause is the one that reads like the hard combinatorial
condition, and for any 2-transitive -- in particular any highly transitive --
action it is free.  What is left is a finite-presentation question about the
acting group, which is the clause every route in this region gets stuck on.

That is exactly the shape of `boone-higman-via-bffhz-action-image`: its
action is highly transitive with finitely generated stabilizers by
`relative-automorphism-action-is-highly-transitive`, so its only open leaf is
`bffhz-action-image-is-finitely-presented`, a finite-presentation claim.  It
is also the shape a sharply 2-transitive construction would have -- sharp
2-transitivity gives the single pair orbit and a trivial point stabilizer,
which is finitely generated for free, leaving finite presentation of the
acting group as the whole problem.  No such construction is claimed here, and
none was verified; the point is that the transitivity is never what is
missing.

Read against `fiber-product-conjugation-action-lemma` this is the opposite
end of the same dial: the fiber-product action has one pair orbit per
conjugacy class, so it is 2-transitive exactly when the normal subgroup has
one nontrivial class, and the lemma's clause 6 is what a 2-transitive action
gets for nothing.
