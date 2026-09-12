---
rg: 2
id: fpbs-conditional-traffic-descent-bound
kind: claim
title: Conditional routing traffic gives a constructive cost bound in the target action
artifacts:
  - research/artifacts/fpbs/docs/shared-component-repair.md
  - research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md
  - research/artifacts/fpbs/responses/51_0909-211602.md
---

Fix a factor map pi from a free action Y onto a free action X of a countably infinite group, with C(X)<infinity. Choose a finite-cost generating base graphing Lambda=(T_(h_i)|D_i). A plan has finitely many source partial transformations T_(g_j)|A_j and chosen paths of one bounded length covering a finite prefix of Lambda-requests on E_i contained in pi^(-1)(D_i). Its budget r is the uncovered prefix measure plus the full tail cost sum_(i>n) mu(D_i), as in Section 9 of the artifact. The finite-generator plan of Sections 2--4 is the special case of finitely many full-domain demands and zero tail. Let N_j be the integer traffic of the edge copy (j,z), let m_j = E[N_j | pi] and p_j = P(N_j > 0 | pi), and let J_pi be the sum over j of the integral of min(1,m_j) - p_j. Then

C(X) <= B + J_pi = r + sum_j integral min(1, m_j) dmu,   where B = r + sum_j nu(N_j > 0).

The construction lives in the target action: retain T_{g_j} where m_j >= 1, drop it elsewhere, and charge the failed generator requests to the omitted traffic through an exact edge-occurrence change of variables. There is no independence assumption on edges or failures and no worst-case route-length multiplier; long routes are charged through their actual traffic. J_pi is nonnegative by conditional Jensen and equals min(P(N_j = 0 | pi), E[(N_j - 1)_+ | pi]) pointwise, the overlap after projection of the absence measure and the repeated-use measure. The threshold 1 is the unit cost of retaining one edge, not a tunable constant.

For the countable demand graphing, apply the repair argument to the finite
prefix and append the entire base demand tail. Its ordinary graphing cost is
already included in r. The completed graphing can have countably many maps;
only the routed part and its traffic are finite. No infinite-cost base is
covered by this extension.

Status records a written deduction, not independent validation. The note reports a finite check of the projection-and-repair construction on 4,096 domain configurations of a six-point two-sheet extension of a regular Z/3 action; that script is not part of this archive, and the check tests finite accounting only.

The repair can also use whole components. If the retained base
graphing F has connected infinite contacts between its components
in a fixed finite-cost generating base graphing, the shared-repair
artifact proves C(X)<=c(F) by repairs of arbitrarily small cost on
X itself. This applies to the threshold graphing above or another
measurable base selection meeting the stated hypothesis. The source
routing data are not asserted to provide that hypothesis.
