---
rg: 2
id: cmm-unique-games-low-value-rounding
kind: claim
title: A polynomial-time randomized rounding satisfies, in expectation, c0 min(1, 1/sqrt(eps log k)) (1-eps)^2 (k/sqrt(log k))^(-eps/(2-eps)) of a (1-eps)-satisfiable unique game on k labels (Charikar--Makarychev--Makarychev 2006, Theorem 3.1)
distinct_from:
  cmm-unique-games-sqrt-log-k-rounding: that is CMM Theorem 4.5, the near-satisfiable regime 1 - O(sqrt(eps log k)), which says nothing once eps log k is large; this is CMM Theorem 3.1, the low-value regime k^(-eps/(2-eps)), which is non-trivial at every eps < 1 including eps near 1/2.
---

**ESTABLISHED, BY CITATION.** There are an absolute constant `c_0 > 0` and a
polynomial-time randomized algorithm with the following property. Take a unique
game on alphabet `[k]` (`k >= 2`), given as a constraint (multi)graph, with an
assignment satisfying at least a `1 - eps` fraction of the constraints
(`0 <= eps < 1`). The algorithm outputs an assignment whose satisfied fraction
`X` obeys

```text
E[X]  >=  g(eps, k)  :=  c_0 · min(1, 1/sqrt(eps ln k)) · (1 - eps)^2 · (k / sqrt(ln k))^(-eps/(2-eps)).
```

The base of the logarithm changes only `c_0`. The algorithm does not need to
know `eps`: the theorem is stated for the optimum `1 - eps*`, and `g` is
non-increasing in `eps` for `k >= 2`, so any `eps >= eps*` may be used.

This is not a new result.

DERIVATION cmm-unique-games-low-value-rounding-citation
