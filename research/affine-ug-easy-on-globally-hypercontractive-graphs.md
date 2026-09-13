---
rg: 2
id: affine-ug-easy-on-globally-hypercontractive-graphs
kind: claim
title: Affine unique games over noisy Johnson, Grassmann and HDX walk graphs are solvable to a constant fraction at any constant completeness (Bafna--Minzer 2023)
distinct_from:
  affine-ug-easy-on-certifiably-hypercontractive-graphs: that needs certified small-set expansion and completeness near 1; this covers graphs that are not small-set expanders but have characterizable non-expanding sets, and works at arbitrarily small constant completeness.
  two-to-two-games-theorem: that is NP-hardness built on Grassmann-graph expansion; this says unique games whose constraint graph is itself Grassmann are easy even at small completeness.
---

**ESTABLISHED, BY CITATION.** Mitali Bafna, Dor Minzer, *Solving Unique Games
over Globally Hypercontractive Graphs*, arXiv:2304.07284v1 (CCC 2024). Affine UG
is UG over `Z_q` with constraints `x_i - x_j = b`.

* **Theorem 1.5.** Take `alpha in (0,1)` and `0 < eps <= eps_0`, and an affine
  UG instance over `J(n, l, alpha l)` that is `(1-eps)`-satisfiable. In time
  `n^(poly(l, |Sigma|, 1/eps))` it finds an assignment satisfying a
  `2^(-O(sqrt(eps)/alpha))` fraction.
* **Theorem 1.6.** For `alpha in (0,1)` and `c > 0` there is `delta > 0` with
  the following guarantee. On a `c`-satisfiable affine UG instance over
  `J(n, l, alpha l)`, in time `n^D` with `D = l^(poly(|Sigma| l^(1/c)))`, it
  finds a `delta` fraction.
* **Theorem 1.7.** The same for `Grass(n, l)`.
* **Theorem 1.8.** The same for the depth-`alpha` canonical walk on
  `d`-dimensional two-sided `gamma`-local-spectral expanders, with
  `gamma << o_l(1)` and `d > l`.

**Bearing.** The authors conclude that UG is easy on globally hypercontractive
graphs, which highlights the importance of graphs that lack such a
characterization in PCP reductions for UG. A proof of `unique-games-conjecture`
must use constraint graphs whose non-expanding small sets are *not* succinctly
characterized, or the running time's dependence on `l` and `|Sigma|` must be
exploited. Their footnote 2 notes that the KKMO reduction to affine UG does not
preserve topology, so general UG on these graphs is not covered.

DERIVATION affine-ug-easy-on-globally-hypercontractive-graphs-citation
