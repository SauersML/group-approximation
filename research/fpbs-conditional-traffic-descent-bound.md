---
rg: 2
id: fpbs-conditional-traffic-descent-bound
kind: claim
title: Conditional routing traffic gives a constructive cost bound in the target action
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md
  - research/artifacts/fpbs/responses/51_0909-211602.md
---

Fix a factor map pi from a free action Y onto a free action X of a finitely generated group and a finite routing plan on Y: finitely many partial transformations T_{g_j} restricted to A_j, chosen paths of one bounded length covering the s-requests on E_s, and uncovered budget r. Let N_j be the integer traffic of the edge copy (j,z), let m_j = E[N_j | pi] and p_j = P(N_j > 0 | pi), and let J_pi be the sum over j of the integral of min(1,m_j) - p_j. Then

C(X) <= B + J_pi = r + sum_j integral min(1, m_j) dmu,   where B = r + sum_j nu(N_j > 0).

The construction lives in the target action: retain T_{g_j} where m_j >= 1, drop it elsewhere, and charge the failed generator requests to the omitted traffic through an exact edge-occurrence change of variables. There is no independence assumption on edges or failures and no worst-case route-length multiplier; long routes are charged through their actual traffic. J_pi is nonnegative by conditional Jensen and equals min(P(N_j = 0 | pi), E[(N_j - 1)_+ | pi]) pointwise, the overlap after projection of the absence measure and the repeated-use measure. The threshold 1 is the unit cost of retaining one edge, not a tunable constant.

Status records a written deduction, not independent validation. The note reports a finite check of the projection-and-repair construction on 4,096 domain configurations of a six-point two-sheet extension of a regular Z/3 action; that script is not part of this archive, and the check tests finite accounting only.
