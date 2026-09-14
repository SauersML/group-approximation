---
rg: 2
id: fournier-facio-simple-factor-not-hyperlinear
kind: claim
title: The finitely presented simple factor of the Fournier--Facio construction is not hyperlinear
distinct_from:
  fournier-facio-has-no-purely-singular-free-near-representation: That is the negative hyperlinearity branch for the whole Fournier--Facio group; this is the strictly stronger assertion about its simple subgroup S, which by wreath heredity kills every nontrivial tracial model of the group.
  fournier-facio-group-hyperlinear: That is the positive branch for the whole group; its truth would force this claim to be false.
artifacts:
  - research/artifacts/fournier-facio-hyperlinearity-survivor-audit-2026-09-11.md
---

Let `S` be the finitely presented infinite simple torsion-free group chosen
in `fournier-facio-torsion-free-skeleton` (a Burger--Mozes or Hyde--Lodha
group).  Then `S` is not hyperlinear.

By `fournier-facio-nontrivial-quotients-contain-simple-wreath` this would
make every homomorphism from the Fournier--Facio group into the unitary group
of an `R^omega`-embeddable finite von Neumann algebra trivial.  In particular
it would close the negative branch.  This is recorded to make that permanence
explicit, not as a promising attack.

## Attempts

Deferred.  A proof would itself produce a first non-hyperlinear group, and
this graph records no normalized-HS obstruction for any finitely presented
infinite simple group.  The compression and commuting-copy structure that
drives the nonsoficity of `G` is not available inside `S`, which has no
compression letter.  The live negative attack stays on the whole group:
`nonhyperlinear-via-fournier-facio-singular-near-state` and the lane
exploring a universal normalized-HS no-go.
