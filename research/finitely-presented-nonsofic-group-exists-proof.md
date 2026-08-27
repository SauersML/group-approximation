---
rg: 2
id: finitely-presented-nonsofic-group-exists-proof
kind: route
title: Cover the finitely generated witness by a finite table
target: finitely-presented-nonsofic-group-exists
requires: [universal-leavitt-el4-nonsofic]
artifacts:
  - GroupApproximation/Covers/TableCover.lean
  - GroupApproximation/Endpoint/MainResults.lean
---

## Why sufficient

The prerequisite gives a finitely generated group `G` that is not sofic.
`Covers/TableCover.exists_finitelyPresented_cover_of_not_isSofic` turns that
into a finitely presented `H` with `not IsSofic H`: the finite-table
construction produces a finitely presented group surjecting onto `G`, and
soficity passes to quotients, so `H` cannot be sofic either.  Finite generation
of `G` is what the construction consumes, and the prerequisite supplies it as
part of its profile.

## Not a restatement

The prerequisite is about one explicit elementary group and does not mention
presentations; a finitely generated nonsofic group is not a finitely presented
one, and the gap between them is exactly the cover construction -- which is a
theorem about arbitrary finitely generated nonsofic groups and would be worth
having even if this witness were replaced.
