---
rg: 2
id: kl-fp-simple-counterexample-via-decidable-counterexample-and-bh
kind: route
title: Take a decidable counterexample and embed it by Boone--Higman
target: kl-counterexample-can-be-finitely-presented-simple
requires: [kl-counterexample-can-have-solvable-word-problem, boone-higman-conjecture, fp-simple-kl-failure-transfers-through-decidable-groups]
---

Suppose the conjecture fails.  By the first prerequisite, it fails over a
finitely generated group `P` with solvable word problem.  By
`boone-higman-conjecture`, `P` embeds in a finitely presented simple group `S`.
By item 2 of the third prerequisite, the failure moves to `S`.

## What it does not need

The full Boone--Higman conjecture is more than needed.  Any finitely presented
simple envelope of the one decidable counterexample suffices, for instance
membership of `P` in the permutational class `B_A` through BFFHZ Theorem C.
That weaker statement is not wired here because no node on main states it as a
claim for an unspecified `P`.
