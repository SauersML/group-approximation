---
rg: 2
id: local-context-hierarchy-converges-to-full-group-norm
kind: claim
title: Increasing vector-context depth recovers exactly the full group C-star norm
distinct_from:
  finite-context-energy-certificate-iff-word-trivial: that characterizes finite quadratic certificates for individual words; this computes the limit of the full constrained vector optimization for every group-ring polynomial and proves finite-level attainment.
  finite-context-relator-energy-misses-nontrivial-words: that gives a fixed finite countermodel; this identifies the entire infinite-depth limit and its full-C-star representation meaning.
  full-mf-radical-uniform-asymptotic-collapse: that concerns global operator-norm defects and full radical collapse; this imposes only relator equations on finitely many orbit vectors, whose limit is the full group C-star norm.
artifacts:
  - research/artifacts/local-context-and-global-norm-hierarchies.md
---

For a finite presentation $G=\langle S\mid R\rangle$ with $m=|S|\geq1$,
let $\beta_n(f)$ be the supremum of $\|f(U)\xi\|^2$ over finite unitary
tuples and unit vectors subject to

$$ (r(U)-I)q(U)\xi=0\qquad(r\in R,\ |q|\leq n). $$

Then $\beta_n(f)\downarrow\|f_G\|_{C^*(G)}^2$, for the **full** group
C-star algebra. At fixed $n$, a maximum is attained in dimension at most

$$D_L=1+\sum_{k=1}^L2m(2m-1)^{k-1},
\quad L=\max(1,\deg f,n+\max_{r\in R}|r|).$$

The empty-relator maximum is zero. Every nontrivial word $w_G$ satisfies
$\beta_n(w-1)\geq2$ at every level and in the limit, including a nontrivial
MF-radical word if one is chosen. No effective convergence rate is asserted.
The dimension bound does not apply to globally small relator norms.
