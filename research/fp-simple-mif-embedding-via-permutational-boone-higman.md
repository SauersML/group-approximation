---
rg: 2
id: fp-simple-mif-embedding-via-permutational-boone-higman
kind: route
title: Permutational Boone--Higman answers BFFHZ Question 3.4, so the V times minimal free SFT premises answer it too
target: fp-simple-groups-embed-in-fp-simple-mif-groups
requires:
  - permutational-boone-higman-conjecture
  - simple-envelope-forces-solvable-word-problem
  - fp-simple-highly-transitive-groups-satisfy-pbh
---

**Route.** The implication is complete and fires once
`permutational-boone-higman-conjecture` is proved. Through
`permutational-boone-higman-via-v-times-aperiodic-sft-full-groups`, that
conjecture follows from two OPEN symbolic-dynamics premises:
- (P1) `decidable-groups-embed-in-fp-groups-with-minimal-free-sft`;
- (P2) `v-times-minimal-free-sft-alternating-full-groups-are-fp`.

So Question 3.4 now reduces to the same two premises as the Boone--Higman route
`boone-higman-via-v-times-aperiodic-sft-full-groups`. Each premise can fail on
its own.

## Proof

Let `S` be a finitely presented simple group.
1. `S` is finitely generated, and it is a finitely generated subgroup of itself.
   By `simple-envelope-forces-solvable-word-problem`, it has solvable word problem.
2. By `permutational-boone-higman-conjecture`, `S` embeds in a group admitting an
   action of type (A).
3. By BFFHZ Theorem C, imported verbatim in
   `fp-simple-highly-transitive-groups-satisfy-pbh`, (i) implies (iv): `S` embeds
   in a finitely presented simple group that is MIF. ∎

## What this changes for the target

- Before this route the target had no route in the graph. Its Attempts record
  only one-group-at-a-time positive cases and kills of particular host classes.
- The reverse implication is already recorded as a cycle:
  `permutational-boone-higman-via-mif-envelopes` gets the permutational
  conjecture from Boone--Higman plus Question 3.4, whose last step can be taken
  as Theorem C, (iv) implies (i). With Zaremsky's Corollary B
  (`boone-higman-via-permutational-boone-higman`) and this route, the
  permutational conjecture is equivalent to the conjunction of Boone--Higman and
  Question 3.4.
- **Calibration.** The route consumes finite presentation of `S` only to get
  solvable word problem. This is consistent with the calibration on the target:
  Question 3.4 for all computably presented simple groups implies Boone--Higman.
  Here both the permutational conjecture and Boone--Higman come out of the same
  premises, so nothing weaker than Boone--Higman has been assumed.
