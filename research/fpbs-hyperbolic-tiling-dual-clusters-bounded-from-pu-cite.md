---
rg: 2
id: fpbs-hyperbolic-tiling-dual-clusters-bounded-from-pu-cite
kind: route
title: Import the three-phase theorem of Benjamini and Schramm for percolation on hyperbolic regular tilings
target: fpbs-hyperbolic-tiling-dual-clusters-bounded-from-pu
requires: []
---

Citation import, not a reproof.

I. Benjamini, O. Schramm, *Percolation in the hyperbolic plane*, J. Amer. Math.
Soc. 14 (2001), arXiv:math/9912233. The arXiv abstract page was read on
2026-09-17. The abstract says, verbatim:

> This is a study of percolation in the hyperbolic plane and on regular tilings
> in the hyperbolic plane. The processes discussed include Bernoulli site and
> bond percolation on planar hyperbolic graphs, invariant dependent percolations
> on such graphs, and Poisson-Voronoi-Bernoulli percolation. We prove the
> existence of three distinct nonempty phases for the Bernoulli processes. In
> the first phase, $p\in(0, p_c]$, there are no unbounded clusters, but there
> is a unique infinite cluster for the dual process. In the second phase,
> $p\in(p_c,p_u)$, there are infinitely many unbounded clusters for the process
> and for the dual process. In the third phase, $p\in [p_u,1)$, there is a
> unique unbounded cluster, and all the clusters of the dual process are
> bounded.

**How the target follows.**

- Item 1 is the third phase.
- Item 2 is the second phase. Since the dual process at `p` is
  Bernoulli(`1-p`) on `G†`, it has unbounded clusters for dual density
  `1-p > 1-p_u` and none for `1-p <= 1-p_u`. This gives `p_c(G†) = 1-p_u`.
- "Three distinct nonempty phases" gives `0 < p_c < p_u < 1`.

**Scope caveat.** The abstract states its hypotheses informally ("regular
tilings in the hyperbolic plane", "planar hyperbolic graphs"). The target is
restricted to regular hyperbolic tilings, the class the abstract names
explicitly. The full theorem in the paper covers planar nonamenable transitive
one-ended graphs. That version is recalled here but not imported.
