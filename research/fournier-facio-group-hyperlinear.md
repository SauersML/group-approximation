---
rg: 2
id: fournier-facio-group-hyperlinear
kind: claim
title: The Fournier--Facio torsion-free nonsofic group is hyperlinear
distinct_from:
  fournier-facio-group-matricially-stable: That is operator-norm stability and is already established; it gives no normalized-Hilbert--Schmidt microstates.
  fournier-facio-universal-frobenius-stable-t-embedding: That concerns unnormalized Frobenius stability of a related universal construction; this asks for canonical normalized-HS models of the concrete nonsofic group.
artifacts:
  - research/artifacts/fournier-facio-hyperlinearity-survivor-audit-2026-09-11.md
---

The finitely presented torsion-free group `G` fixed in
`fournier-facio-torsion-free-skeleton` has canonical normalized-Hilbert--
Schmidt microstates, equivalently its group von Neumann algebra embeds in
`R^omega`.

The established operator-norm and unnormalized-Frobenius stability theorems
do not decide this claim.  Its exact state-form witness is isolated by
`fournier-facio-hyperlinear-iff-singular-near`.

## Attempts

The live attack is
`fournier-facio-hyperlinear-from-singular-near`: build the purely singular
amenable near representation isolated by the exact criterion.  The obvious
stability transfer is unavailable.  Operator-norm asymptotic triviality and
unnormalized Frobenius stability allow no conversion of a normalized-HS
microstate defect, because a defect supported on `o(d)` dimensions is cheap
in normalized HS and remains order one in both of those stronger metrics.

**Necessary structure (2026-09-11).**  `G` contains the wreath product
`S wr Z` of its simple factor by the compression letter `t_1`
(`fournier-facio-group-contains-simple-wreath-shift`), and every nontrivial
quotient of `G` contains it faithfully
(`fournier-facio-nontrivial-quotients-contain-simple-wreath`).  So this
positive branch requires the simple factor `S` to be hyperlinear.  Every
nontrivial tracial model also carries a proper Hilbert-hotel shift on the
`Gamma`-commutant, with relative commutants growing by copies of `L(S)`
(`fournier-facio-regular-models-carry-commutant-shift`).  The survivor audit
in the linked artifact shows that the recorded witness fences use `G` only
through nonsoficity and torsion-freeness.  It also recommends an
infinite-component witness in which `t_1` acts as a bilateral tensor shift,
built on the self-similar tail `Gamma >= J_1 x t_1 Gamma t_1^-1`.
