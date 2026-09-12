---
rg: 2
id: thompson-v-r5-cap-implies-one-word-collapse
kind: claim
title: Coherent alternating packets force the coarse Thompson swap to collapse in matrices
artifacts:
  - research/artifacts/thompson-v-r5-coherent-alternating-packet-2026-08-21.md
distinct_from:
  thompson-v-r5-coherent-alternating-packet: that is the open synchronization input; this is the completed representation-degree reduction from that input to one-word normalized-HS collapse.
  thompson-v-one-word-strict-hs-ceiling: that asks directly for some strict scalar ceiling; this records the stronger conclusion that the Bleak--Quick coarse swap converges to the identity under CAP.
---

If `thompson-v-r5-coherent-alternating-packet` holds, then for the coarse swap
`a=(00 01)` every sequence of finite-dimensional models of the fixed
Bleak--Quick presentation with relator defect tending to zero satisfies

```text
||U(a)-I||_2 -> 0.                                      (TCAP)
```

In particular CAP implies `thompson-v-one-word-strict-hs-ceiling` for the word
`a`.
