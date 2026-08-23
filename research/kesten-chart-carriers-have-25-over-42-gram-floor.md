---
rg: 2
id: kesten-chart-carriers-have-25-over-42-gram-floor
kind: claim
title: Kesten chart carriers have a twenty-five-over-forty-two Gram floor
artifacts:
  - research/kesten-chart-intersection-floor-proof.md
distinct_from:
  stabilizer-orbit-commutators-have-a-kesten-chart-carrier: that constructs the stabilizer-invariant Kesten quantile and leaves all conjugate-carrier intersections open; this computes the orbit size, proves most conjugate free subgroups intersect trivially, and obtains a strict overlap floor.
  two-equivariant-shell-pvms-have-independent-coordinate-escape: that constructs an added independent-coordinate model for two hypothetical shell PVMs; this proves unavoidable centered independence for 1,050 ordered pairs inside the native raw graph-product model itself.
---

**ESTABLISHED FIREWALL.**  In the notation of
`stabilizer-orbit-commutators-have-a-kesten-chart-carrier`, the orbit

```text
O=D.(h^(-1)C)
```

has exactly

```text
m=16.                                                  (KIF1)
```

Let the 42 chart anchors be `a_i=g_i hC`, let `O_i=g_iO`, and let

```text
K_i=<[c_(a_i),c_z]:z in O_i> isomorphic to F_16.       (KIF2)
```

The orbital relation `a_j in O_i` is symmetric and has valency 16.  For
every distinct pair outside that relation,

```text
a_j notin O_i   ==>   K_i cap K_j={1}.                (KIF3)
```

Consequently, if `E_i in L(K_i)` are the conjugate Kesten quantile
projections of trace `p=1/42`, then for each of the 1,050 ordered pairs in
`(KIF3)` one has

```text
tau(E_iE_j)=tau(E_i)tau(E_j)=1/42^2.                  (KIF4)
```

All remaining projection overlaps are nonnegative.  Therefore the mixed
Gram scalar from `(KCC8)` satisfies the dimension-free exact lower bound

```text
G_K=sum_(i!=j)tau(E_iE_j)
   >=1050/42^2
    =25/42.                                           (KIF5)
```

In particular

```text
||sum_i E_i-1||_2^2>=25/42.                           (KIF6)
```

Thus the native Kesten carriers cannot be the forty-two chart PVM and
cannot approach it.  No further analysis of the 336 unordered exceptional
orbit pairs is needed for this conclusion.  Those are exactly the pairs
`a_j in O_i`, and their intersections are nontrivial because the two free
bases contain the inverse pair of commutators

```text
[c_(a_i),c_(a_j)]  and  [c_(a_j),c_(a_i)].            (KIF7)
```

This common commutator has infinite order in either free group.  The
exceptional intersections can only increase `(KIF5)`.  Hence the full
stabilizer-orbit nonlinear spectral construction resolves negatively: it
recreates an independent-refinement floor of at least `25/42` before any
phase-tag ledger is applied.
