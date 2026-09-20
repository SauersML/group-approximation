---
rg: 2
id: leavitt-lcs-game-with-certified-numerical-gap
kind: claim
title: Freeze a Leavitt-derived binary linear-system game with a certified rational dimension-independent quantum gap
distinct_from:
  binary-lcs-perfect-qc-strict-qa-gap-exists: That supplies existence and a non-displayed positive gap; this requires explicit equations, source words and a rational gap certificate.
  explicit-exact-support-lcs-witness: That requires a submenu extracted from a specific BCS exact-support mass argument; this uses a finitely presented Leavitt radical word, a central HNN tag and the solution-group embedding.
artifacts:
  - research/artifacts/liu-to-linear-games-and-marked-gap-2026-09-20.md
---

Produce a finite binary matrix A, vector b, rational full-support question
law, and rational epsilon > 0 for the resulting finite game, together with:

1. exact source presentation and words identifying a nontrivial Leavitt
   radical word;
2. a central-tag presentation and Slofstra embedding words with finite
   relator-filling certificates;
3. proof of a perfect commuting strategy;
4. a dimension-independent proof that every finite-dimensional quantum
   strategy has loss at least epsilon.

This is OPEN. No numeric matrix list, epsilon or all-dimension certificate
has been produced by the September 20 integration.

## First attack and stopping rule

The source is the reviewed four-generator/eighteen-relator
Leavitt presentation, not the unreviewed smaller presentations. The literal
generator x=1+S[00]T[01] is nontrivial and needs no word search. All source homomorphisms are trivial by
`binary-leavitt-tracial-ultraproduct-images-are-trivial` (Jihao Liu's analytic
input plus the recorded ring argument). The first checkpoint is now
`leavitt-central-sign-seed-for-lcs`: a specified six-generator,
twenty-five-relator central-tag presentation. The remaining word-map
manifest is the output of the Slofstra embedding, not the source mark.

The involutive central tag costs twice the source collapse modulus plus one
relator defect, by `central-hnn-tag-transfers-hyperlinear-radical`. The
existing fixed-word embedding estimate then propagates it linearly in
relator defect. These are proved interfaces, not the remaining obstacle.
The missing quantitative datum is a proved numerical source collapse
bound and a quantitative near-perfect-strategy decoder for the chosen
game convention. Compactness supplies their existence in the needed form,
not displayed constants or a terminating general certificate search.

Do not run unbounded game enumeration or dimension sampling as a proof.
First freeze a small source certificate manifest, then extract constants
symbolically; any bounded computation is only a sanity check. Do not infer
perfect-completeness RE-hardness from this single fixed game.
