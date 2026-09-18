---
rg: 2
id: fpbs-reuse-removal-from-compact-and-weakly-mixing-steps
kind: route
title: Remove reuse flags one Furstenberg-Zimmer step at a time, compact steps and relatively weakly mixing steps separately
target: fpbs-correlated-reuse-flags-removable
requires:
  - fpbs-compact-extensions-preserve-cost
  - fpbs-relatively-weakly-mixing-extensions-preserve-cost
  - fpbs-compact-weakly-mixing-tower-decomposes-cost-preservation
  - fpbs-traffic-variational-cost-identities
artifacts:
  - research/artifacts/fpbs-furstenberg-zimmer-cost-tower-2026-09-17.md
---

For a finitely generated group every free action has finite cost. The two open halves supply P_c and P_w for every such group. The established decomposition then gives C(Y) = C(X) for every free factor Y -> X. The zero-gap criterion of `fpbs-traffic-variational-cost-identities` turns equality into the requested plans. Lifts of near-optimal base plans have zero defect and budget tending to C(X) = C(Y).

This is a genuine decomposition into two prerequisites that can each fail independently of the other. It is not a restatement. Each prerequisite is implied by the target. Their mechanisms differ: invariant finite-rank modules versus small relative correlations. The recorded removal countermodels bear only on the compact half (artifact Section 3). The weakly mixing half already contains fixed price among weakly mixing actions (artifact Section 4).
