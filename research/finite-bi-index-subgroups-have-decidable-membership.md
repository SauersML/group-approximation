---
rg: 2
id: finite-bi-index-subgroups-have-decidable-membership
kind: claim
title: A finitely generated subgroup with finitely many double cosets in a group with solvable word problem has decidable membership
distinct_from:
  conjugacy-finite-recursive-presentation-solvable-wp: that decides the WORD problem of a recursively presented group from finitely many conjugacy classes; this decides MEMBERSHIP in a subgroup from finitely many double cosets, and assumes the word problem is already solvable.
  simple-core-bi-index-counts-coset-action-pair-orbits: that identifies the pair-orbits of a coset action with double cosets; this turns finiteness of those double cosets into a decision procedure for the point stabilizer.
---

Let `Gamma` be a finitely generated group with solvable word problem, and let
`S <= Gamma` be finitely generated with `|S \ Gamma / S| < infinity`. Then the
membership problem for `S` in `Gamma` is decidable.

## Consequences

1. **Type (A) stabilizers.** Suppose an action of `Gamma` has type (A) in the
   sense of `type-a-action-gives-boone-higman-for-subgroups`. That claim gives
   `Gamma` a solvable word problem. For a point `x`, the double cosets
   `Gamma_x \ Gamma / Gamma_x` are the `Gamma`-orbits of ordered pairs in the
   orbit `Gamma x`, and finitely many orbits of two-element subsets leave
   finitely many of them. So every point stabilizer of a type (A) action has
   decidable membership.
2. **Finite bi-index envelopes.** In `boone-higman-via-finite-bi-index-envelope`
   the finitely presented group `Gamma` embeds in the finitely presented simple
   group `SV_Gamma`, so it has solvable word problem by
   `simple-envelope-forces-solvable-word-problem`. Hence
   `ck-envelope-simple-core-has-finite-bi-index` can only hold for an envelope
   in which the simple core `S` has decidable membership in `Gamma`. Any
   arrangement whose core membership problem is undecidable is excluded before
   a single double coset is counted.
3. **Where decidability of the input enters.** The input `G <= S` has solvable
   word problem by hypothesis. The extra effective requirement this route
   imposes is decidable membership of the whole core `S` in its finitely
   presented envelope. A sufficient condition, checkable on a construction, is
   that `S` is undistorted in `Gamma`: if `|u|_S <= C|u|_Gamma + C` on `S`,
   then `w in S` iff `w` equals some word of length at most `C|w|_Gamma + C` in
   the generators of `S`, which is a finite search using the word-problem
   algorithm.
