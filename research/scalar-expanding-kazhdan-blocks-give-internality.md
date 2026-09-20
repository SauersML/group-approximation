---
rg: 2
id: scalar-expanding-kazhdan-blocks-give-internality
kind: claim
title: "Matching approximate scalar-expanding Kazhdan blocks recovers the full commutant"
distinct_from:
  at-op62-holds-for-representation-lifts: "That assumes genuine representations in every coordinate; here the blocks are approximate and are supplied only with scalar gaps."
artifacts:
  - research/artifacts/liu-internality-normalization-audit-2026-09-20.md
---

## Attribution

Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf) (2026-09-20), Lemma 6.4 and Proposition 6.5. This node records or conditionally uses Liu's result; it does not claim that analytic contribution for Cairn.

Fix a homomorphism pi of a finitely generated Kazhdan group into a specified tracial matrix ultraproduct. Suppose its generator lifts admit reducing block decompositions after a vanishing total squared HS perturbation, with discarded trace tending to zero and one FIXED positive scalar gap on every nonzero retained block. Then pi(H)' cap M is internal in those matrix dimensions.

The coordinate blocks need only satisfy group relations asymptotically; unequal ranks are allowed. The conclusion captures off-diagonal multiplicity intertwiners, not merely diagonal scalar matrices. Liu Proposition 6.5 uses Lemma 6.4 to bound initially unbounded HS witnesses, obtain asymptotically equal ranks for matching blocks, align each cluster with a least-rank representative, and generate coherent matrix units W_i W_j^*.

## Attempts

2026-09-20: equation-level inspection is recorded in the cited audit. No concrete gap was found in the inspected steps, but this import remains OPEN pending completion of its independent review. No empty-premise citation route is supplied.
