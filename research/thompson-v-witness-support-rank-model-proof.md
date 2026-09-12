---
rg: 2
id: thompson-v-witness-support-rank-model-proof
kind: route
title: Apply the averaging lemma inside the support subgroup and exhibit the rank targets
target: thompson-v-linear-witness-supports-kill-g-in-rank-models
requires:
  - full-averaging-idempotent-kills-its-element-in-rank-models
  - monomial-rank-models-are-hamming-models
artifacts:
  - research/artifacts/thompson-v-rank-support-and-kernel-transfer-2026-09-12.md
---

The witness equation already holds in `F_p[H]`, and the averaging lemma kills `g` in every rank
model of `H`. The rank targets:
- finite quotients of `H` give regular permutation representations;
- characteristic-`p` representations are rank targets directly;
- sofic or LEF approximations of `H` give ultraproducts of permutation matrices, whose rank distance
  from the identity is at least half the Hamming distance (`monomial-rank-models-are-hamming-models`),
  so each is injective on `H`;
- a linear sofic approximation is injective by definition.

Each of these would keep `g` alive. Artifact Section 2.
