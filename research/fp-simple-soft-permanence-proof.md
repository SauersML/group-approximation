---
rg: 2
id: fp-simple-soft-permanence-proof
kind: route
title: Relators plus one surviving word pin a neighbourhood to S, and a nontrivial map to an amenable group is injective
target: fp-simple-groups-escape-soft-hyperlinear-permanence
requires: []
---

Write `S = <X | R>` with `X` and `R` finite, and fix a word `w` with
`w != 1` in `S`.

**Isolation.**  In the space of marked groups on `X`, the conditions "every
`r in R` is trivial" and "`w` is nontrivial" are finitely many basic
conditions, so they define an open set `U`.  A marked group in `U` is a marked
quotient `S/N` with `w notin N`.  Then `N` is a proper normal subgroup of the
simple group `S`, hence trivial, so `U = {S}`.

**Residual collapse.**  If `S` is residually amenable, choose a homomorphism
to an amenable group that does not kill `w`.  Its kernel is a proper normal
subgroup, hence trivial, so `S` embeds in an amenable group and is amenable.
If `S` is LEA, take a local embedding into an amenable group `A` of a ball
containing `w` and every relator path.  Sending the generators to their
images respects all relators, so it defines a homomorphism `S -> A` that does
not kill `w`, and the first case applies.
