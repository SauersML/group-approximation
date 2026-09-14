---
rg: 2
id: kun-thom-clifford-cover-has-no-finitary-site-structure
kind: claim
title: The Kun--Thom Clifford cover admits no finitary site structure
distinct_from:
  finitary-split-extension-surjunctivity-permanence: that proves surjunctivity for split extensions that carry a finitary site structure; this proves the Clifford cover carries none, so that theorem cannot reach it.
  kun-thom-clifford-cover-weakly-sofic: that concerns weak soficity and nonsoficity of the same group; this concerns the surjunctivity permanence machinery.
artifacts:
  - research/artifacts/clifford-cover-surjunctivity-test-host-2026-09-12.md
---

Let `Gamma < G` be the Kun--Thom Theorem E pair and `X = G/Gamma`. Let `S` be a `G`-invariant graph on
`X` with at least one edge, and `E_S = Vtilde_S semidirect G` the Clifford cover of
`kun-thom-clifford-cover-weakly-sofic`, with central involution `eps`.

Then `E_S` carries no finitary structure (conditions (A1)–(A3) of
`finitary-split-extension-surjunctivity-permanence`) for any choice of site projections and support
function. So `E_S` lies outside that permanence theorem and its wreath instance.

Proof: artifact Section 1. Condition (A2) forces two translated anticommuting lamps to die in every site
projection, and B. H. Neumann's covering lemma supplies the translate. Hence every projection kills `eps`,
and (A1) fails.
