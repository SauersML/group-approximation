---
rg: 2
id: kazhdan-commutants-are-internal
kind: claim
title: "Every finitely generated Kazhdan group has internal commutants in tracial matrix ultraproducts"
distinct_from:
  at-op62-holds-for-representation-lifts: "That proves the genuine-coordinate special case; this quantifies over arbitrary approximate lifts."
  kt-centralizer-normalization-hs: "That is invariance under ambient conjugation; this describes the coordinate algebra of the commutant."
  actor-commutant-has-liftable-masa-in-every-model: "That is a weaker partition-object claim at a particular pair with vertex-rounding assumptions; this is full internality for every Kazhdan homomorphism."
artifacts:
  - research/artifacts/liu-block-construction-audit-2026-09-20.md
  - research/artifacts/liu-internality-normalization-audit-2026-09-20.md
  - research/artifacts/liu-cairn-integration-2026-09-20.md
---

## Attribution

Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf) (2026-09-20), Theorem 1.2 / 6.7. This node records or conditionally uses Liu's result; it does not claim that analytic contribution for Cairn.

**OPEN: Liu's Theorem 1.2 / 6.7, under independent review.**

For every finitely generated discrete group H with property (T), every nonprincipal ultrafilter omega on N, every sequence d_n>=1 and every homomorphism pi:H->U(M), where M=prod_omega(M_(d_n),tr_(d_n)), there are unital *-subalgebras A_n<=M_(d_n) with
```
pi(H)' cap M = [A_n]_omega.
```
The dimensions and ultrafilter are the specified originals. Pi need not be injective or preserve the regular character. The conclusion does NOT assert that supplied generator lifts are genuine representations or that their uncorrected exact coordinate centralizers suffice.

## Connections

This shared analytic premise feeds compression normalization and sequential Kazhdan heat rounding. It does not by itself assert dimension-free rounding of arbitrary bistochastic channels. The integration guide traces the two downstream group routes and their distinct scopes.

## Attempts

2026-09-20: bounded parallel audits inspected §§3–8 and the Leavitt interface; no concrete gap was located in the inspected steps. The long analytic imports and their external inputs have not received complete independent certification. The graph therefore records conditional assembly and leaves these prerequisites OPEN rather than importing the whole paper as an empty-premise proof.
