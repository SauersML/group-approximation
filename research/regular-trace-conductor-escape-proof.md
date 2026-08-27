---
rg: 2
id: regular-trace-conductor-escape-proof
kind: route
title: Average many fixed root elements and exhibit a drifting nearest-neighbor flow
target: regular-trace-allows-diffuse-dyadic-flow
requires:
  - sparse-dyadic-iwahori-packets-have-a-uniform-boundary
---

Fix `r` and let `P_(n,<=r)` be the central reducing projection onto all
constituents of conductor at most `r`.  Choose any `N` distinct elements

```text
g_j=u(2^r j) in Gamma(2^r),              0<=j<N,
A_n=(1/N) sum_j Pi_n(g_j).                              (RTP1)
```

Every `g_j` acts trivially on `P_(n,<=r)`, so

```text
A_n P_(n,<=r)=P_(n,<=r),
tr(P_(n,<=r)) <= ||A_n||_2^2.                           (RTP2)
```

On the other hand,

```text
||A_n||_2^2=(1/N^2)sum_(i,j) tr(Pi_n(g_i^(-1)g_j)).     (RTP3)
```

The `N` diagonal terms converge to one and every off-diagonal term converges
to zero, because `g_i^(-1)g_j` is a fixed nonidentity element.  Thus

```text
limsup_n tr(P_(n,<=r)) <= 1/N.                          (RTP4)
```

Since `N` is arbitrary, `(RTE1)` follows.  Notice that this proof avoids
character cancellation: it uses the positive second moment of the root
average.

For `(RTE2)`, every interior row and column has two entries of size
`1/(2K)` and each endpoint has one.  Hence both marginals lose exactly
`1/(2K)` at each of two endpoints, giving common mass `(K-1)/K` and
unmatched mass `u=1/K`.  In a row, the portion weakly below the diagonal is
either zero or `1/(2K)`; the same statement holds for the weakly-above
portion of a column.  This verifies the two-thirds inequalities directly.

For the integral strengthening `(RTE4)`, let `L>=2` and index the occupied
depths by `1,...,L`.  Set

```text
c_(1,1)=2,  c_(1,2)=1,
c_(a,a-1)=c_(a,a)=c_(a,a+1)=1       (1<a<L),
c_(L,L-1)=c_(L,L)=1.
```

Every row and column below the top has total three; the top row and column
have total two.  The weakly lower part of each row and weakly upper part of
each column has total exactly two, so `(SBP4)--(SBP5)` are saturated.  The
common mass is `3L-1` and the unmatched mass is one on each side, proving
`(RTE4)` after normalization by `3L`.

Finally, if `h` is a fixed nonidentity element of `SL_2(Z)`, residual
finiteness of its congruence image gives `r(h)` such that its reduction is
nonidentity modulo `2^a` for every `a>=r(h)`.  Inside `Reg(G_a)`, the sum of
all irreducibles factoring through `G_(a-1)`, with their regular
multiplicities, is an inflated copy of `Reg(G_(a-1))`; its orthogonal
complement `Sigma_a` is an actual representation supported only at exact
conductor `a`.  For `a-1>=r(h)`, both regular characters vanish at `h`, so
`chi_(Sigma_a)(h)=0`.  Since the support in `(RTE2)` lies above `A_n`,
choosing `A_n->infinity` proves the asserted pointwise regular-trace
compatibility.
