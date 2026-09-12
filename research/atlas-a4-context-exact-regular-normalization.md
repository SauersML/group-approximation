---
rg: 2
id: atlas-a4-context-exact-regular-normalization
kind: claim
title: Atlas A4 context exactifications may be normalized to exact regular type at every finite-group vertex
artifacts:
  - research/artifacts/a4-context-virtually-free-compiler-2026-08-19.md
---

Let `d_n=20160 k_n` and let `sigma_n` be a simultaneous exactification of a
canonical regular-atlas sequence in the fixed A4 context graph of groups.
Then there are exact representations `sigma'_n` of the same graph-of-groups
fundamental group on the **same** `d_n`-dimensional spaces such that

```text
max_(x in fixed presentation generators)
  ||sigma_n(x)-sigma'_n(x)||_2 -> 0,
```

and every finite vertex group has exactly its regular representation type:

```text
A8 vertex:  k_n Reg(A8),
A4 vertex:  1680 k_n Reg(A4).
```

Moreover stable letters which were `o(1)` from the identity remain `o(1)` from
the identity after normalization.

Thus the local representation-type residuals can be removed completely, not
merely made `o(d_n)`.  After this step the atlas context compiler has a single
external parameter `k_n`; all remaining freedom is carried by exact unitary
intertwiners between fixed regular restrictions.
