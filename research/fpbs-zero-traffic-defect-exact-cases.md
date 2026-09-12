---
rg: 2
id: fpbs-zero-traffic-defect-exact-cases
kind: claim
title: The conditional descent defect vanishes exactly for single-use or fiberwise-present edges
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md
  - research/artifacts/fpbs/responses/51_0909-211602.md
---

For one edge label and almost every base point the local defect min(P(N_j = 0 | pi), E[(N_j - 1)_+ | pi]) vanishes if and only if either the conditional traffic is at least one almost everywhere on the fiber, or it takes only the values 0 and 1 there; integrality of traffic makes the two cases exhaustive. So an uncertain edge that serves a single request may be discarded and its request repaired directly at no extra cost, whatever its conditional presence probability, and an arbitrarily reused edge descends without loss as soon as its presence is visible in the base. The alternatives may be used on different sets and for different labels, and a positive defect requires absence and repeated use to be mixed at the same projected point and edge label. An edge used k >= 2 times on a fiber fraction p and unused otherwise has local penalty exactly min(1 - p, (k-1)p). Preserving every correlation is therefore far stronger than what descent needs.

Status records a written deduction, not independent validation.
