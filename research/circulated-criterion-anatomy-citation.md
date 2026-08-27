---
rg: 2
id: circulated-criterion-anatomy-citation
kind: route
title: Import the source anatomy from a second-hand relay, corroborated where possible
target: circulated-criterion-condition-iii-locus
requires: []
artifacts:
  - research/artifacts/collapse-criterion-source-2026-08-16.md
  - GroupApproximation/Sofic/AscendingHNNStabilizer.lean
---

## What was and was not read

The circulated PDF is **not** in this repository and was not read here.  What
was read is a structured relay dated 2026-08-16, transcribed into
`research/artifacts/collapse-criterion-source-2026-08-16.md`, carrying
internal anchors: Theorem 4.1 for the criterion, Lemma 3.2 for the commuting
projection lifts, Lemma 2.1 / Corollary 2.2 for the matricial Mautner step,
Lemma 5.1 for the `EL_3` generation, and lines 509--526 for the word estimate.
Those anchors are reported, not verified.

## Why the import is nevertheless safe

Three of the load-bearing pieces are corroborated inside this repository,
independently of the relay:

- the witness-site identification `Stab_Gamma(t Gamma) = alpha(Gamma)` is
  kernel-checked as `AscendingHNNStabilizer.smul_tSite_eq_iff`;
- the word estimate and its multi-mover replacement are reproved in sections 5
  and 7 of `multi-mover-hnn-dossier-2026-08-15.md`, and the block-repair
  endpoint is Lean-checked;
- the matricial Mautner step is proved from scratch in
  `matricial-mautner-fixed-subspace`, so nothing downstream rests on the
  reported lemma numbers.

What the relay adds that is genuinely new to the project is the *location*
claim — that (iii) is consumed once, in the estimate — and the identity of the
concrete instance (`EL_3(F_2[x,y])` with `y |-> xy`), which is a different
realization of the same structural input from the affine index-eight doubling
used in-repo.

## Trust surface

This route establishes a statement **about a document**.  If the primary is
later obtained and the anatomy differs, this card and only this card is
affected: no mathematical claim in the graph takes it as a prerequisite.
