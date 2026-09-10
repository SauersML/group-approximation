---
rg: 2
id: fpbs-reuse-flag-localization-preserves-cost
kind: claim
title: Nearly optimal cost survives compression to finitely many binary edge-reuse observables
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-reuse-localization.md
  - research/artifacts/fpbs/docs/fixed-price-reuse-compression.md
  - research/artifacts/fpbs/responses/55_0909-215618.md
---

Let pi from Y to X be a factor map of free actions of a finitely generated group. For every epsilon > 0 there is an intermediate factor Y -> Z -> X with C(Y) <= C(Z) < C(Y) + epsilon, where Z is generated over X by the group translates of finitely many binary observables, and these may be taken to be the reuse flags B_j = {N_j >= 2} of one finite routing plan of budget below C(Y) + epsilon. Conditioning on Z makes the traffic defect exactly zero at every edge copy: on B_j the conditional traffic is at least two so the presence probability is one, and off B_j it lies in {0,1}. The flag measures satisfy sum_j nu(B_j) <= B, and accumulating the flags of a sequence of plans gives one intermediate factor with C(Z) = C(Y) exactly.

The route, the exact traffic values, and the domains of singly used edges need not be measurable in Z; discarded single-use edges are repaired directly. This is compression, not erasure: the orbit name of even one binary observable can carry complicated long-range constraints, the fibers of Z over X need not be finite, and Z need not be a proper factor of Y.

Status records a written deduction, not independent validation. `research/artifacts/fpbs/scripts/verify_reuse_compression.py`, with the results in `research/artifacts/fpbs/docs/fixed-price-reuse-compression-checks.json`, exercises the retained-reuse-plus-repair construction on all 4,096 domain pairs of a six-point two-sheet free Z/3 action; that is a finite check of the equivariant accounting only.
