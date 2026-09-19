---
rg: 2
id: weighted-equality-gap-forbids-separated-port-mass
kind: claim
title: A weighted equality spectral gap forbids separated positive port mass
distinct_from:
  sparse-ports-either-lose-soundness-or-repeat-relative-pieces: that treats unweighted counting density and expander ball packing; this gives the metric obstruction for arbitrary reversible edge weights.
  regular-tree-consistency-has-vanishing-spectral-gap: that uses one centroid cut in a tree; this applies to any weighted equality graph once two positive-mass port sets are far apart.
---

Let a reversible weighted equality graph have stationary probability `mu`,
Dirichlet form

```text
E(f)=1/2 sum_{uv} c_uv |f(u)-f(v)|^2,
```

and spectral gap `gamma`.  Suppose two port sets `Q_0,Q_1` satisfy

```text
mu(Q_0)>=c,       mu(Q_1)>=c,       dist(Q_0,Q_1)>=R.           (WEG1)
```

Then

```text
gamma <= C/(c R^2)                                                (WEG2)
```

for a universal normalization constant `C`.

Consequently, a port-weighted equality decoder with fixed spectral gap
cannot send two positive portions of the tested ports to growing graph
distance.  In the complete Pauli table every pair of ports in one logical
cloud participates in a mixed rectangle, so making all relevant peripheral
segments long/unique is incompatible with a uniform pairwise-equality
agreement modulus.

The result does not exclude a higher-arity locally testable code.  It shows
that such a code, rather than a reweighting of equality edges, is required to
escape the finite-piece obstruction.

