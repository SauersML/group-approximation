---
rg: 2
id: anti-central-corner-gives-invisible-kernel-pair
kind: route
title: A solution of the anti-central swap corner transfers to an invisible kernel pair
target: ternary-anti-central-kernel-unitization-not-directly-finite
requires: [ternary-anti-invariant-swap-corner-is-full, ternary-anti-central-failures-transfer-into-kernel-corners]
artifacts:
  - research/artifacts/ternary-anti-central-kernel-normal-forms-2026-09-12.md
---

From `c e_- b = eps_-`, put `a = e_- b` and `c' = c e_-`.
* Then `c' a = eps_-`.
* `a c' != eps_-`: if `e_- (b c e_-) = eps_-`, then `e_- = eps_-`, which is false.

So `S_-` is not directly finite, and the Klein-corner transfer
(`ternary-anti-central-failures-transfer-into-kernel-corners`) turns this pair into an invisible
pair over `eps_-`. Section 4 of the artifact.
