---
rg: 2
id: bht-trivial-normal-intersection-envelope
kind: claim
title: Solvable word problem is equivalent to embedding in a finitely presented group while missing every proper normal subgroup
distinct_from:
  boone-higman-conjecture: that requires the finitely presented overgroup itself to be simple; this allows many proper normal subgroups but requires every one of them to miss the embedded input, so its maximal simple quotients need not be finitely presented.
  proper-normal-subgroups-miss-the-normally-generating-core: that is the elementary lattice lemma deducing trivial intersections from a simple core containing one ambient normal generator; this is the universal existence theorem producing such an ambient finitely presented group for every finitely generated solvable-word-problem input, together with the converse algorithm.
  boone-higman-thompson-simple-envelope: that produces a finitely generated computably presented simple envelope; this produces a finitely presented nonsimple ambient group whose every nontrivial quotient preserves the original input.
---

For a finitely generated group `Gamma`, the following are equivalent:

1. `Gamma` has solvable word problem;
2. there are an embedding `Gamma <= P` and a finite presentation of `P` such
   that

   ```text
   N <| P and N != P  implies  N intersect Gamma = 1;
   ```
3. `Gamma` embeds in every nontrivial quotient of one finitely presented
   overgroup `P`.

Equivalently, one may choose a chain

```text
Gamma <= G <= P
```

where `G` is finitely generated and simple, `P` is finitely presented, and
every nonidentity element of `G` normally generates `P`.

This is a property-`(T)`-free universal near-solution of Boone--Higman.  A
maximal proper normal quotient of `P` is simple and still contains `Gamma`;
the unresolved point is exactly whether one such maximal kernel can be
finitely normally generated, hence whether one such simple quotient is
finitely presented.

