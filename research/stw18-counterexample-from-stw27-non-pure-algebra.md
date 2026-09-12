---
rg: 2
id: stw18-counterexample-from-stw27-non-pure-algebra
kind: route
title: A strict-comparison algebra that is not pure is not Z-stable, so it refutes Toms--Winter
target: stw18-strict-comparison-non-z-stable-algebra-exists
requires: [stw27-strict-comparison-non-pure-algebra-exists, rank-density-and-strict-comparison-give-purity]
artifacts:
  - research/artifacts/toms-winter-rank-density-firewall-2026-09-11.md
---

Take `A` from the first prerequisite: unital, simple, separable, nuclear,
non-elementary, stably finite, with strict comparison, and not pure.  Suppose
`A` were `Z`-stable.

1. N. P. Brown, F. Perera, A. S. Toms, J. reine angew. Math. 621 (2008),
   arXiv:math/0609182, Theorem 5.5, read in this lane: for a simple unital
   exact finite `Z`-stable algebra the rank map
   `W(A)_+ -> LAff_b(T(A))^{++}` is surjective.
2. In particular every continuous strictly positive affine function on `T(A)`
   is exactly a rank function, so rank density holds.
3. The second prerequisite then makes `A` pure, contradicting the hypothesis.

So `A` is not `Z`-stable while having strict comparison, and it witnesses the
target.  This makes the XXVII(1) negation root a sharper form of the XVIII
negation root.
