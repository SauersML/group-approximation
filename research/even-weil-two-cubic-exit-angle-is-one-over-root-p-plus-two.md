---
rg: 2
id: even-weil-two-cubic-exit-angle-is-one-over-root-p-plus-two
kind: claim
title: The two neutral even-Weil cubic exits have cosine one over root p plus two
distinct_from:
  two-cubic-residual-carriers-recover-the-deleted-source: that gives an abstract decoder under a principal-angle hypothesis; this computes the hypothesis exactly for the determinant-neutral Weil packets.
  deleted-fixed-line-first-cubic-has-explicit-positive-spectrum: that computes one carrier's residual spectrum; this computes the relative position of the two carriers.
  direct-sum-weil-compressions-have-quadratic-padding: that adds defect and padding sizes; this proves source authentication and a uniform cross-carrier gap.
---

Let `p=1 mod 8`, let `q=delta_0`, and use the full even-Weil tuple
`(X,R,S)` and its polar compression `(X_0,R_0,S_0)` to `PH` from
`even-weil-fixed-line-compression`.  Put

```text
W_1=(X_0S_0^2)^3,             W_2=(X_0R_0S_0)^3,
Z_i=ran(W_i-1),                V=P X q.                (EWA1)
```

Then `dim Z_1=dim Z_2=2`, their intersection is exactly `V`, and their
other principal cosine is

```text
cos_exit(Z_1,Z_2)=1/(sqrt(p)+2).                       (EWA2)
```

In particular, since `p>=17`,

```text
cos_exit <= 1/(sqrt(17)+2)<1/6.                        (EWA3)
```

Thus the carrier-product decoder in
`two-cubic-residual-carriers-recover-the-deleted-source` has a universal
spectral gap on every determinant-neutral canonical packet.

The conclusion survives arbitrary orthogonal sums, heterogeneous primes,
and multiplicities.  The source is the direct sum of the source lines, and
the largest non-source principal cosine is the maximum of the block cosines,
hence still below `1/6`.  Simultaneous unitary mixing of multiplicity copies
conjugates both carrier projections and leaves these principal angles
unchanged.  Therefore neither heterogeneous prime levels nor multiplicity
gauge can make the canonical neutral Weil exits asymptotically parallel.

