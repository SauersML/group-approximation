---
rg: 2
id: cmm-unique-games-sqrt-log-k-rounding-citation
kind: route
title: Import Theorem 4.5 of Charikar--Makarychev--Makarychev, Near-Optimal Algorithms for Unique Games (STOC 2006)
target: cmm-unique-games-sqrt-log-k-rounding
requires: []
---

Literature import, credited in full.

Moses Charikar, Konstantin Makarychev, Yury Makarychev, *Near-Optimal
Algorithms for Unique Games*, Proceedings of the 38th ACM Symposium on Theory of
Computing (STOC 2006), pp. 205--214. Verified on 2026-09-17 from the authors'
PDF, https://home.ttic.edu/~yury/papers/unique.pdf:

* Abstract: "For instances with domain size k where the optimal solution
  satisfies 1-ε fraction of all constraints, our algorithms satisfy roughly
  k^{-ε/(2-ε)} and 1-O(sqrt(ε log k)) fraction of all constraints."
* **Theorem 4.5.** "There is a polynomial time algorithm that finds an
  assignment of variables which satisfies 1 − O(√(ε log k)) fraction of all
  constraints if the optimal solution satisfies (1 − ε) fraction of all
  constraints."
* Proof of Theorem 4.5: "Summing the probabilities obtained in Lemma 4.2 over
  all edges (u,v) and using the concavity of the function √x we get that the
  expected number of satisfied constraints is 1 − O(√(ε log k)) |E|."
* Definition 1.1: a unique game is a constraint graph `G = (V,E)` with a
  permutation `π_uv` of `[k]` on each edge.

A bipartite unique game with edge multiset `E` is such a constraint graph.
Parallel edges are handled by their multiplicity in the sum over edges, so the
expectation bound holds for multigraphs. The rounding is randomized and the
proof bounds the expectation, which is the form recorded in the claim. `square`
