---
rg: 2
id: range-cover-deficit-syndrome-proof
kind: route
title: Compress the witness to local ranges and dominate its shifted separator by kernel penalties
target: range-cover-deficit-certifies-no-finite-syndrome-cost
requires: [local-syndrome-synthesis-has-an-exact-sdp-test]
artifacts:
  - research/artifacts/qpcp-fixed-term-chain-2026-09-07.md
---

Lemma 1 proves the claim directly. Finite domination bounds each marginal
by its range projection, while exclusion of the empty fault set forces
their sum to dominate identity. The witness state contradicts these two
bounds. For the explicit dual, compression of
`rho-sum_a P_a rho P_a` to every charged range is nonpositive. A scalar
identity shift makes it strictly negative there. The displayed kernel
penalties dominate the remaining blocks by Cauchy--Schwarz, giving positive
trace and zero denominator in the earlier weak dual theorem.
