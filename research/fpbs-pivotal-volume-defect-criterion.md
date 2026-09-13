---
rg: 2
id: fpbs-pivotal-volume-defect-criterion
kind: claim
title: Mean convergence of finite-volume pivotals is exactly control of the bypass excess
artifacts:
  - research/artifacts/fpbs/docs/global-pivotal-tails-and-volume-defect.md
---

Fix a nonamenable transitive graph and a uniqueness parameter
p in (p_c,1). For fixed vertices v,w and a nested finite vertex
exhaustion V_R, let E_R be connection in its induced open graph,
Z_R its open pivotal count (zero outside E_R), E global connection,
and Z the global open pivotal count (zero outside E).

Then B_R=Z_R-Z 1_(E_R) is nonnegative and is eventually zero almost
surely. Global pivotals are integrable, and

    E_p[Z_R | E_R] -> E_p[Z | E]
      iff E_p B_R -> 0
      iff {B_R} is uniformly integrable
      iff {Z_R} is uniformly integrable.

The assertion also holds for the independent lazy-walk endpoint X_n
at each fixed n. It asserts no uniform-integrability hypothesis and
no convergence uniform in n or p. It identifies the exact finite-volume
obligation when applying the global pivotal tail to the existing OPEN
near-critical growth target `fpbs-universal-subcritical-pivotal-growth-rate`.
