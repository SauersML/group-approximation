---
rg: 2
id: cmm-unique-games-sqrt-log-k-rounding
kind: claim
title: A polynomial-time randomized rounding satisfies 1-O(sqrt(eps log k)) of a (1-eps)-satisfiable unique game in expectation (Charikar--Makarychev--Makarychev 2006)
distinct_from:
  unique-games-conjecture: that asserts hardness at 1-eps vs eps for some k(eps); this is the algorithm forcing that k(eps) grows like exp(Omega(1/eps)).
---

**ESTABLISHED, BY CITATION.** There is an absolute constant `A` and a
polynomial-time randomized algorithm with the following property. Take a unique
game on alphabet `[k]`, given as a constraint (multi)graph, that has an
assignment satisfying at least a `1 - eps` fraction of the constraints. The
algorithm outputs an assignment whose satisfied fraction `X` obeys

```text
E[1 - X]  <=  A sqrt(eps log k).
```

This is the expected-value form. CMM's proof of Theorem 4.5 bounds the expected
number of satisfied constraints.

This is not a new result.

DERIVATION cmm-unique-games-sqrt-log-k-rounding-citation
