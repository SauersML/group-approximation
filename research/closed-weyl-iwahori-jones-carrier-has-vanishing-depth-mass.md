---
rg: 2
id: closed-weyl-iwahori-jones-carrier-has-vanishing-depth-mass
kind: claim
title: The canonical closed-Weyl Iwahori Jones carrier has exponentially vanishing dyadic-depth mass
distinct_from:
  fixed-spherical-polynomials-have-no-42nd-projection: that rules out a fixed group-word polynomial projection of trace one over forty-two using connected Satake spectrum; this constructs the genuine Jones projection in the basic construction and computes why its common six-direction mass vanishes with dyadic depth.
  native-sl3-edge-parahoric-has-index-forty-two: that computes the six depth-one parahorics separately and their depth-one intersection; this treats arbitrary depth and identifies the exact loss incurred by demanding one Jones carrier for every Weyl direction simultaneously.
  infinite-index-canonical-subgroup-corner-is-impossible: that rules out a positive canonical corner for one infinite-index subgroup in an arbitrary crossed product; this gives an explicit finite-index exhaustion inside SL3 and the quantitative bound two to the minus two N.
---

Put

```text
C=SL_3(Z),                 h=diag(2,1,1/2),
lambda=(1,0,-1),           h_w=w h w^(-1)              (JCD1)
```

for signed Weyl permutations `w in S_3`.  At depth `N>=1`, define

```text
D_(N,w)=C cap h_w^N C h_w^(-N),
K_N=intersection_(w in S_3) D_(N,w).                   (JCD2)
```

Then

```text
K_N={g in SL_3(Z): 2^(2N) divides g_ij for every i!=j}.
                                                               (JCD3)
```

In particular

```text
[C:K_N]>=2^(2N).                                       (JCD4)
```

Let `e_N` be the Jones projection from `L^2(L(C))` onto `L^2(L(K_N))`
inside the basic construction.  With its canonical normalized trace,

```text
Tr(e_N)=1/[C:K_N] <=2^(-2N).                           (JCD5)
```

The `C/K_N` conjugates of `e_N` are the genuine orthogonal coset PVM, so
this construction really does authenticate all six depth-`N` Weyl charts
on one common Fourier carrier.  However, the carrier mass tends to zero.
More precisely, the distinguished base atom has no depth-uniform positive
lower bound under the normalized trace of its natural finite-index basic
construction.

## Divisibility and index

For `g in C`, membership in `D_(N,w)` is equivalent to

```text
v_2(g_ij)>=N max(0,lambda_(w,i)-lambda_(w,j))          (JCD6)
```

for every `i!=j`.  Given an ordered pair `(i,j)`, some Weyl permutation
places weight `1` at `i` and weight `-1` at `j`; the maximum in `(JCD6)`
over all `w` is therefore `2N`.  This proves `(JCD3)`.

The left cosets

```text
x_12(t)K_N,             0<=t<2^(2N),                  (JCD7)
```

are distinct: their pairwise quotients are `x_12(t-s)`, which lie in `K_N`
exactly when `2^(2N)` divides `t-s`.  This proves `(JCD4)`, and the standard
finite-index Jones trace formula gives `(JCD5)`.

## Exact scope

At each fixed `N`, Jones induction is a valid canonical support
authentication mechanism.  It may be realized in a matrix amplification
using a `C/K_N` coset transversal, with `e_N` represented by one coordinate
projection.  Hence the obstruction is not existence of finite-depth shell
coordinates.

What fails is depth-uniform positive mass for the distinguished atom.
The saturated arithmetic actor contains every `h_w^N`, and `(JCD5)` shows
that the normalized mass of the corresponding common base atom tends to
zero in its natural depth-`N` amplification.  Summing all coset atoms
restores total trace one, but then transporting that whole PVM by the
denominator is exactly the global `A/C` Schreier-PVM problem, not a single
Iwahori spectral projection.  The established building gap can consume
such a PVM only after it has been lifted in the matrix coordinates with
covariance controlled by presentation defect.

This also fences the regular-HNN/Bernoulli leak.  Its tracial basic
construction contains the same Jones projections and satisfies `(JCD5)`;
therefore their abstract existence cannot distinguish a matrix ultraproduct
from that leak.  The missing input remains coordinatewise lifting of the
full coset PVM (or an equivalent cross-chart Gram estimate), not another
spectral cutoff in the limiting von Neumann algebra.
