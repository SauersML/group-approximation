---
rg: 2
id: cmm-unique-games-low-value-rounding-citation
kind: route
title: Import Theorem 3.1 of Charikar--Makarychev--Makarychev, Near-Optimal Algorithms for Unique Games (STOC 2006)
target: cmm-unique-games-low-value-rounding
requires: []
---

Literature import, credited in full.

Moses Charikar, Konstantin Makarychev, Yury Makarychev, *Near-Optimal
Algorithms for Unique Games*, Proceedings of the 38th ACM Symposium on Theory of
Computing (STOC 2006), pp. 205--214. The same PDF as
`cmm-unique-games-sqrt-log-k-rounding-citation`,
https://home.ttic.edu/~yury/papers/unique.pdf. Its text was re-extracted on
2026-09-20 with pdfminer. The quotes below are from that text stream. Line
breaks and the typesetting of fractions are normalised.

* Abstract: "For instances with domain size k where the optimal solution
  satisfies 1 − ε fraction of all constraints, our algorithms satisfy roughly
  k^{−ε/(2−ε)} and 1 − O(√(ε log k)) fraction of all constraints."
* **Theorem 3.1.** "There is a polynomial time algorithm that finds an
  assignment of variables which satisfies
  Ω( min(1, 1/√(ε log k)) · (1 − ε)^2 · (k/√(log k))^{−ε/(2−ε)} )
  fraction of all constraints if the optimal solution satisfies (1 − ε)
  fraction of all constraints."
* Proof of Theorem 3.1, last step: "Summing this probability over all edges
  (u, v) in E0 and using convexity of the function (1−x)^2 f_k(x) we get the
  statement of the theorem." Here "this probability" is `P_uv`, the
  probability that Rounding Algorithm 1 satisfies the edge `(u,v)`. So the
  bound is on the **expected** number of satisfied constraints.
* Definition 1.1: "A unique game consists of a constraint graph G = (V, E), a
  set of variables x_u (for all vertices u) and a set of permutations π_uv on
  [k] = {1, . . . , k} (for all edges (u, v)). Each permutation π_uv defines
  the constraint π_uv(x_u) = x_v."
* Rounding Algorithm 1, step 2: "Pick random independent Gaussian vectors
  g_1, . . . , g_k". So the rounding is randomized.

**Reading used by the target.**

1. `Ω` is read as follows: there is an absolute constant `c_0 > 0` such that
   the bound holds with `c_0` in front, for all `k >= 2` and all `ε`.
2. The proof sums a per-edge probability over the edge list. So the bound holds
   for constraint multigraphs, with each parallel edge counted once. This is
   the same reading as the Theorem 4.5 import.
3. The bound is on the expected satisfied fraction. Any stronger reading, such
   as "with high probability", implies the expected form after changing `c_0`.

**Consistency remark (not used by the target).** Section 5 ("d to 1 Games") of
the same paper states: "We will show how to satisfy
Ω( 1/√(log k) · (1 − ε)^4 · (k/√(log k))^{−(d−1+ε)/(d+1−ε)} ) fraction of all
constraints (the multiplicative constant in the Ω notation depends on d).
Notice that this value can be obtained by replacing ε in formula (1) with
ε' = 1 − (1 − ε)/d (and changing (1 − ε)^2 to (1 − ε)^4)." At `d = 2` the
exponent is `(1+ε)/(3−ε)`. The target re-derives this exponent from Theorem 3.1
alone, through orientation lifts.
