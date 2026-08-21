---
rg: 2
id: native-hecke-edge-rank-integrality-is-bounded
kind: claim
title: The native Hecke edge gives only bounded rank divisibility because its orbital graph has bounded cliques
distinct_from:
  commuting-conjugate-involution-is-balanced-overlap: that computes the four atoms for one edge; this audits whether iterating those atoms can yield unbounded finite-dimensional rank pressure and proves that the direct clique iteration cannot.
  marked-clifford-table-exponential-dimension: that has arbitrarily large pairwise Pauli packets and hence unbounded exponential capacity; the native graph has uniformly bounded complete subgraphs.
  native-sl3-group-is-hecke-graph-wreath-product: that identifies the graph-wreath structure; this extracts the rank consequence of local finiteness.
---

Let `Theta_h` be the `A`-orbital graph of `{C,hC}`.  Since `C` and
`hCh^-1` are commensurable,

```text
L_+=[C:C cap hCh^-1] < infinity,
L_-=[C:C cap h^-1 C h] < infinity.                     (BRI1)
```

The neighbors of the base vertex lie in the two finite Hecke shells

```text
C h C/C     and     C h^-1 C/C,
```

so

```text
deg(Theta_h) <= L_+ + L_-.
```

In particular every clique has size at most

```text
omega(Theta_h) <= 1+L_++L_- < infinity.                (BRI2)
```

For a `k`-clique, the corresponding lamp involutions commute.  Canonical
trace tests on all nonempty products make their `2^k` joint sign projections
asymptotically equidistributed, producing the expected fixed divisibility/
rank pressure `2^k`.  But `(BRI2)` bounds `k` by a constant depending only on
the one Hecke orbital.  Spectator amplification absorbs every such fixed
divisibility constraint.

Therefore the native relation `[c,h c h^-1]=1` cannot yield an unbounded
Clifford/Boolean capacity breaker merely by conjugating it and taking joint
spectral atoms.  Any proof of the interior-overlap exclusion must use global
actor covariance/expansion across NONCOMMUTING graph regions, not a larger
commuting clique hidden in the same orbital graph.
