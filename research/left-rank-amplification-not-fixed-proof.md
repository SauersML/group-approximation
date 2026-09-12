---
rg: 2
id: left-rank-amplification-not-fixed-proof
kind: route
title: Compute the range and fixed vectors of a left-multiplication spectral projection
target: left-rank-amplification-is-not-a-fixed-sector
requires: []
---

For `Y in M_d`, direct multiplication gives

```text
S(h)L_XS(h)^*(Y)
 =U(h)XU(h)^*Y
 =XY,
```

which proves `(LRA2)`.  If `p=p^*=p^2`, then `L_p` is an orthogonal
projection for the Hilbert--Schmidt inner product.  Its range consists of
the matrices whose columns lie in `p C^d`, so its rank is `rank(p)d`; after
normalization by `d^2` this is `tr_d(p)`.

The identity `S(h)L_p=L_pS(h)` follows from `p in U(H)'`.  On the other
hand, a vector `Y in Ran(L_p)` is fixed precisely when

```text
pY=Y,                    U(h)YU(h)^*=Y for all h,
```

which is `(LRA6)`.  For a diagonal unitary with simple spectrum the second
condition says that `Y` is diagonal.  Exactly the first `m` diagonal matrix
units lie in `pM_d`, proving `(LRA7)--(LRA8)`.
