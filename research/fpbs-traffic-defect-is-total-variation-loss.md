---
rg: 2
id: fpbs-traffic-defect-is-total-variation-loss
kind: claim
title: The conditional traffic penalty equals a total-variation loss between absence and reuse
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-reuse-compression.md
  - research/artifacts/fpbs/responses/54_0909-215309.md
---

For a finite routing plan put sigma_j = (N_j - 1) nu, so that the pushforward is (m_j - 1) mu. Then J_pi = (1/2) sum_j ( |sigma_j|(Y) - |pi_* sigma_j|(X) ), by the identity min(1,t) = (1 + t - |t - 1|)/2. The Jordan decomposition is explicit: the positive part (N_j - 1)_+ nu is usage beyond the first request, the source of the savings from sharing, and the negative part is the unused-edge event; they are disjoint on Y and the penalty is exactly their overlap after projection, sum_j integral min(a_j, b_j) dmu with a_j = P(N_j = 0 | pi) and b_j = E[(N_j - 1)_+ | pi]. For a fixed plan and nested information sigma-algebras above the base, the penalty decreases as information grows, by the L1 contraction of conditional expectation, and these increments telescope. Deciding on which side of the cancellation a source point lies does not require the exact traffic magnitude. The monotonicity does not licence exchanging the limit over information with the optimisation over plans.

Status records a written deduction, not independent validation. The verification script and its results file check the total-variation, overlap and information-chain identities on 3,840 weighted traffic cases and 15,360 nested-information cases in exact rational arithmetic.
