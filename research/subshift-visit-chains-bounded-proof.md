---
rg: 2
id: subshift-visit-chains-bounded-proof
kind: route
title: Bounded visit chains off the minimal subsets, by compactness and uniform recurrence
target: subshift-visit-chains-are-bounded-off-every-minimal-subset
requires: []
artifacts:
  - research/artifacts/sk-k2-recurrent-2026-09-13.md
---

Direct proof; full version in `research/artifacts/sk-k2-recurrent-2026-09-13.md` §1.

**(a) ⇒ (b).** Suppose J-chains of visits to V of every length exist.
1. Let V_m be the set of points of V starting a J-chain of length m at time 0. It depends on the window [0,mJ], so it is clopen. The V_m are decreasing and nonempty. König's lemma over the finitely many gap sequences gives z ∈ V with visits at times 0 = t_0 < t_1 < …, all gaps ≤ J.
2. Let w = lim T^{m_k}z with m_k → ∞. For fixed N and large k, every interval of length J in [−N,N] contains a visit of T^{m_k}z to V. Pass to a subsequence and use that V is clopen: w visits V in every interval of length J. The same holds for every point of cl O(w).
3. A minimal M ⊆ cl O(w) meets V. Since V ∩ Y = ∅, M ⊄ Y, contradicting (a).

**(b) ⇒ (a).** Let M be minimal with M ⊄ Y. Then M ∩ Y = ∅, so some clopen V ⊆ X∖Y meets M. By uniform recurrence a point of M ∩ V visits V syndetically, which gives chains of every length. □
