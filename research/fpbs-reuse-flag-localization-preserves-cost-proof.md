---
rg: 2
id: fpbs-reuse-flag-localization-preserves-cost-proof
kind: route
title: Reveal only the repeated-use flags and apply the descent bound to the intermediate factor
target: fpbs-reuse-flag-localization-preserves-cost
requires:
  - fpbs-conditional-traffic-descent-bound
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-reuse-localization.md
  - research/artifacts/fpbs/docs/fixed-price-reuse-compression.md
  - research/artifacts/fpbs/scripts/verify_reuse_compression.py
---

Section 3 of the reuse-localization artifact and Section 4 of the reuse-compression artifact, the latter also giving the direct construction on Z: keep T_{g_j} exactly where the flag is one, repair the disconnected generator requests, and observe that an unflagged used edge has traffic exactly one, so the traffic identity bounds the repair bill by r + sum_j nu(N_j = 1). The intermediate factor is the pushforward under y mapped to its base point together with all translated flag values, a standard probability factor, free because it factors onto a free action. This is a supplied deduction plus a finite verification script, not external validation.
