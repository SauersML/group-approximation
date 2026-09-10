---
rg: 2
id: atlas-embedding-upgrade-toolkit-proof
kind: route
title: Subgroup closure in both directions, plus the individual embedding theorems
target: atlas-embedding-upgrade-toolkit
requires:
  - free-product-with-f2-upgrade
---

## Why sufficient

**The upward-passage half.**  Let `P` be subgroup-closed and `H <= G`.  If `G`
had `P` then `H` would, so `H` failing `P` forces `G` to fail `P`.  This is the
whole content of Regime 1: any construction that *contains* `H` preserves the
failure, whatever else it does.

**The blocking half.**  Let `Q` be subgroup-closed and suppose `G` has `Q` and
contains `H`.  Then `H` has `Q`.  So a witness for `!P and Q` produces a group
that fails `P` and has `Q`, and no embedding of a `P`-failing `H` into a
`Q`-group can exist unless `H` itself already has `Q`.  Regime 2 cells are
therefore exactly as hard as building a new example.

**The individual upgrades.**  Each row of the table is a cited theorem, applied
to an arbitrary countable `H`.

* Higman--Neumann--Neumann (1949): every countable group embeds in a 2-generated
  group.
* Every countable group embeds in a 2-generated simple group (P. Hall; Schupp).
* Baumslag--Dyer--Heller (1980) / Kan--Thurston: every group embeds in an
  acyclic group.
* Iterated HNN adjunction of roots embeds any countable group in a countable
  divisible group.
* `free-product-with-f2-upgrade` for the C\*-side, `F_2`, growth, and the
  failure of property (T).
* `H x Z` has centre containing `Z` and amenable radical containing `Z`;
  `H x (sum of countably many Z)` is additionally not finitely generated, since
  it has a non-finitely-generated quotient.
* On `S = sum over N of copies of a nontrivial H`, shifting coordinates down is
  surjective with kernel the first factor, so `S` is not Hopfian; shifting up is
  injective with proper image, so `S` is not co-Hopfian.  Both need only that
  `H` is nontrivial.

## What the classification does not claim

It is not a claim that Regime 2 cells are *false*, only that embedding cannot
reach them.  Nor is the Regime 3 list stable: it shrinks whenever a new
embedding theorem is proved, which is exactly why those are the ones worth
attacking.
