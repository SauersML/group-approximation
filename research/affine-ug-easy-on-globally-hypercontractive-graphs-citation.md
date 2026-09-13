---
rg: 2
id: affine-ug-easy-on-globally-hypercontractive-graphs-citation
kind: route
title: Import Theorems 1.5--1.8 of Bafna--Minzer, Solving Unique Games over Globally Hypercontractive Graphs (arXiv:2304.07284)
target: affine-ug-easy-on-globally-hypercontractive-graphs
requires: []
---

Literature import, credited in full.

Mitali Bafna, Dor Minzer, *Solving Unique Games over Globally Hypercontractive
Graphs*, arXiv:2304.07284v1 (14 April 2023); CCC 2024, LIPIcs vol. 300,
Article 3.

Verified from the arXiv PDF, pages 3--5, on 2026-09-12:

* Definition 1.4 (Affine-UG): alphabet `Z_q`, constraints
  `phi_e(sigma) = sigma + b_e`.
* **Theorem 1.5** (noisy Johnson, completeness near 1), **Theorem 1.6**
  (noisy Johnson, completeness `c > 0`), **Theorem 1.7** (`Grass(n, l)`,
  completeness `c > 0`), and **Theorem 1.8** (random walks on two-sided
  local-spectral HDX), with the running times and fractions quoted in the
  claim. `D = l^(poly(|Sigma| l^(1/c)))`, and footnote 3 says `D` was not
  optimized.
* The abstract: "Our result suggests that UG is easy on globally
  hypercontractive graphs, and therefore highlights the importance of graphs
  that lack such a characterization in the context of PCP reductions for UG."
* Page 3 lists "certain Cayley graphs over the symmetric group" among
  globally hypercontractive graphs. Page 4, footnote 2, says the KKMO reduction
  does not preserve topology.
