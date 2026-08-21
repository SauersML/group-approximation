---
rg: 2
id: regular-tree-consistency-has-vanishing-spectral-gap
kind: claim
title: Finite regular-tree occurrence charts cannot robustly synchronize
distinct_from:
  stabilizer-generator-control-has-unbounded-address-loss: that gives coherent rotation along a long stabilizer word; this gives an averaged consistency countermodel on every large finite bounded-degree tree chart.
  two-transitive-occurrence-sections-have-unbounded-pair-holonomy: that concerns dense pair transport; this rules out the opposite holonomy-free choice of unique tree addresses.
---

Let `T` be a finite connected subtree of a locally finite tree, with
`N=|V(T)|` and maximum degree `Delta`.  Its edge expansion and normalized
Laplacian gap tend to zero uniformly with `N`; quantitatively there is a
vertex set `A` with

```text
(N-1)/Delta <= |A| <= N/2,       |partial_T A|=1,               (RTC1)
```

and hence

```text
lambda_2(T) <= 2 Delta/(N-1)                                    (RTC2)
```

up to the harmless convention used to regularize leaf degrees.

There is also a direct reflection-valued cheating strategy.  Put one Pauli
reflection on `A` and a different Pauli reflection on its complement.  All
occurrence-equality edges except the single cut edge pass exactly, although a
positive fraction of the occurrence operators remain a fixed normalized-HS
distance apart.  The average consistency loss is `O(1/N)`.

Therefore unique free-monoid/tree addresses remove section holonomy only by
removing the expander synchronization needed by occurrence-local Pauli
dimension games.  A regular-tree metapixel needs additional cross-links or a
recursive test whose soundness is not ordinary graph agreement.

