---
rg: 2
id: parity-twist-copies-the-old-commutant-into-the-excess
kind: claim
title: The parity twist copies the entire old commutant into an orthogonal excess commutant
distinct_from:
  macroscopic-projection-is-one-adjoint-direction: that shows one half-rank matrix is only one adjoint direction; this produces as many excess directions as the whole old commutant.
  property-t-hs-positive-density-commutant-no-growth: that forbids a supplied positive-density excess space in approximate HNN models; this constructs the excess space algebraically from the parity implementer.
  predicate-rank-jump-forces-adjoint-reynolds-gap: that creates a positive-density difference between two finite-packet commutants; this is the parity-compressor mechanism which can transport such a difference.
---

In an exact finite-dimensional representation of the parity-headed base, cut
to the central `J=-1` carrier and write

```text
C_0=End_(rho(Lambda))(V),
C_1=End_(rho(alpha(Lambda)))(V).                         (PTC1)
```

Let `q` be the parity implementer and choose `p in Lambda` with `chi(p)=1`.
Then

```text
C_0 directSum C_0 q <= C_1,                              (PTC2)
```

and the sum is orthogonal in Hilbert--Schmidt inner product.  In particular,

```text
dim(C_1)-dim(C_0) >= dim(C_0).                           (PTC3)
```

Indeed `alpha(Lambda)<=Lambda`, `q` centralizes `alpha(Lambda)`, and right
multiplication by `q` is an isometry.  Every element of `C_0` is fixed by
`Ad(p)`, while every element of `C_0q` is negated because `pq=-qp` on the
marked carrier.  Their inner product is therefore zero.

The same calculation is quantitatively robust before taking kernels.  For
matrices `X,Y` and any `g in Lambda`,

```text
||[Xq,rho(alpha(g))]||_2
 <= ||[X,rho(alpha(g))]||_2
    +||X||_op ||[q,rho(alpha(g))]||_2,                  (PTC4)
```

and if `Y` is almost fixed while `Xq` is almost negated by `Ad(rho(p))`,

```text
2|<Y,Xq>|
 <= ||Ad(rho(p))Y-Y||_2 ||Xq||_2
    +||Ad(rho(p))(Xq)+Xq||_2 ||Y||_2.                  (PTC5)
```

Thus spectral cutoff and polar-alignment losses are the only analytic costs
in promoting a positive-density old commutant to a positive-density excess
space.  Combined with property-`(T)` commutant no-growth, any lower bound

```text
dim(C_0)/dim(V)^2 >= eta>0                              (PTC6)
```

forces a dimension-independent normalized-HS defect.  The parity candidate
does not currently supply `(PTC6)`; without it, `(PTC2)` may still consist of
only `O(1)` adjoint directions.
