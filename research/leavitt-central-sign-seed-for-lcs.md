---
rg: 2
id: leavitt-central-sign-seed-for-lcs
kind: claim
title: A specified six-generator twenty-five-relator Leavitt HNN seed has a nontrivial central involution invisible in every tracial matrix model
distinct_from:
  central-hnn-tag-transfers-hyperlinear-radical: That is the general marked-word construction; this fixes the reviewed eighteen-relator Leavitt presentation and its literal generator x.
  leavitt-lcs-game-with-certified-numerical-gap: That requires a completed finite linear-system output and numeric game gap; this supplies only the explicit group input for its wagon-wheel stage.
artifacts:
  - experiments/nonsofic-certificates/presentations/thompson-steinberg-presentation.json
  - research/artifacts/liu-to-linear-games-and-marked-gap-2026-09-20.md
---

Let P=<a,b,c,x|R> be exactly the four-generator/eighteen-relator
presentation in the cited JSON (`relators[*].word`, with uppercase letters
not used and `^-1` denoting inverses), identified with the Leavitt units by
`thompson-steinberg-presentation-of-leavitt-unit-group`.

Define the group K on {a,b,c,x,J,t} by the 25 relators

```
R, J^2,
[J,s] for s in {a,b,c,x},
[t,J],
t x t^-1 J^-1 x^-1.
```

Here [u,v]=uvu^-1v^-1. There are six generators and
18+1+4+1+1=25 relators. The element J is a nontrivial central
involution, and every homomorphism from K to a tracial matrix ultraproduct
kills J. The source mark is the literal generator x, so no search for a
word expressing a rank-four matrix is needed at this interface.

This is a fully specified finite group seed, not an emitted binary matrix A
or an explicit winning-probability bound. Its proof imports the reviewed
presentation completeness and Jihao Liu's analytic theorem through the
whole-Leavitt hyperlinear-radical result. The construction is the standard
central-tag stage of the Paddock--Slofstra reduction.
