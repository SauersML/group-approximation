---
rg: 2
id: finitely-presented-nonsofic-group-exists
kind: claim
title: A finitely presented nonsofic group exists, unconditionally
distinct_from:
  universal-leavitt-el4-nonsofic: That is the explicit finitely GENERATED witness with its full property profile; this is the finitely PRESENTED existence statement, which needs the finite-table cover on top of it and names no group.
  finitely-presented-sofic-non-mf: That is about the manuscript's group E, which IS sofic and fails MF instead; this is about a group that fails soficity itself.
  literal-group-not-sofic: That claim asserts nonsoficity of one specific group, the manuscript's E; this is an existence statement whose witness is the Leavitt cover and says nothing about E.
  hnn-extension-finite-presentation-permanence: That is a permanence statement for HNN extensions, with no approximation property in it; this is an existence statement about nonsofic groups, and its finite presentation comes from the finite-table cover rather than from any HNN construction.
  literal-central-mark-corona-invisible: That is about corona invisibility of a central mark in the non-MF lane; this is about soficity, and the two share no object.
  literal-group-fails-mf-conventions: That records which MF conventions the manuscript's E fails, and E is sofic; this asserts existence of a group that fails soficity itself.
  boone-final-group-finitely-presented: That is finite presentability of the Boone tower, a group whose word problem is the point and whose soficity is not at issue; this is existence of a finitely presented group that fails soficity.
artifacts:
  - GroupApproximation/Endpoint/MainResults.lean
  - GroupApproximation/Covers/TableCover.lean
---

ESTABLISHED, unconditionally and kernel-checked:
`Endpoint/MainResults.exists_finitelyPresented_nonsofic_group`,

    there is a group `H` with `Group.IsFinitelyPresented H` and `not IsSofic H`.

Two weaker forms are stated alongside it and are what the historical headline
asks for: `nonsofic_groups_exist` (some group is not sofic) and
`countable_nonsofic_groups_exist` (some *countable* group is not sofic, the
witness being the ambient group of Theorem A, whose countability is the first
conjunct of its profile).

## Why the finite-table cover is needed at all

The explicit witness of [[universal-leavitt-el4-nonsofic]] is finitely
generated, not finitely presented.  `Covers/TableCover` supplies the missing
step: a finitely generated nonsofic group has a finitely presented nonsofic
cover, by the finite-table construction
(`exists_finitelyPresented_cover_of_not_isSofic`, which retains the quotient
map).  Nonsoficity is inherited upward because soficity passes to quotients.

## Its place in the two programs

This is the endpoint of the `PropertyTT/` development, not of the non-MF
manuscript, and it is independent of the Q3.4 goal: a nonsofic group is not by
itself a *hyperlinear* nonsofic group, which is what
[[hyperlinear-nonsofic-group]] asks for.  It is recorded here because the
graph should know which existence statements the development already owns
outright.
