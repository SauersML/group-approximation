---
rg: 2
id: small-set-expansion-hypothesis-implies-ugc-citation
kind: route
title: Import Theorem 1.4 of Raghavendra--Steurer, Graph Expansion and the Unique Games Conjecture (STOC 2010)
target: small-set-expansion-hypothesis-implies-ugc
requires: []
---

Literature import, credited in full.

Prasad Raghavendra, David Steurer, *Graph Expansion and the Unique Games
Conjecture*, Proceedings of the 42nd ACM Symposium on Theory of Computing
(STOC 2010), pp. 631--640.

Verified from the authors' PDF, pages 2--3, on 2026-09-12:

* Problem 1, `Gap-Small-Set Expansion (eta, delta)`: "Given a graph G and
  constants eta, delta > 0, distinguish whether `Phi_G(delta) >= 1 - eta` or
  `Phi_G(delta) <= eta`."
* Conjecture 1.3 (Gap-Small-Set Expansion Conjecture): "For every eta > 0,
  there exists delta such that the problem Gap-Small-Set Expansion (eta, delta)
  is NP-hard."
* Conjecture 1.2 (Unique Games Conjecture): "For all constants eps, eta > 0,
  there exists large enough constant R such that Unique Games (R, 1-eps, eta) is
  NP-hard."
* **Theorem 1.4.** "The Gap-Small-Set Expansion conjecture implies the Unique
  Games Conjecture."

Also verified, from arXiv:1011.2586v1 (Raghavendra--Steurer--Tulsiani,
*Reductions Between Expansion Problems*), page 6: "Corollary 3.3. The
Small-Set Expansion Hypothesis is equivalent to Hypothesis 3.1 (Unique Games
with Small-Set Expansion)." That is the conference paper at CCC 2012.

Conjecture 1.2 with `eta = eps` is `unique-games-conjecture`. Conversely, the
root's statement gives Conjecture 1.2 for every pair `(eps, eta)` by using
`min(eps, eta)`.
