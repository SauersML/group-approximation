---
rg: 2
id: stw74-relative-grassmannian-bundle-threshold
kind: claim
title: Relative Grassmannian extension controls bundle constraints and first raises the threshold in dimension three
distinct_from:
  stw74-finite-point-ranks-no-topological-obstruction: that proves finitely many fibres can always be corrected without changing an ambient bundle class; this identifies the exact extension obstruction for a positive-dimensional constraint and exhibits a genuine threshold jump.
artifacts:
  - research/artifacts/stw74-property-sp-cu-stability-audit-2026-08-30.md
---

Let `X` be a connected finite CW complex, let `Y` be a nonempty connected
subcomplex, and let

```text
p in C(Y,M_m)
```

be a projection of constant rank `r>=1`.  Define

```text
B_p={f in C(X,M_m): f(y) in C p(y) for every y in Y}.
```

For `k>=1`, the algebra `M_k(B_p)` contains a nonzero projection if and only
if there are an integer `1<=alpha<=k` and a rank-`alpha` projection
`a in C(Y,M_k)` such that the Grassmannian map

```text
y |-> a(y) tensor p(y)
       in Gr_(alpha r)(C^(km))                           (GE)
```

extends continuously from `Y` to `X`.  Equivalently, the bundle
`A tensor E_p` must extend as a rank-`alpha r` subbundle of the fixed trivial
bundle `X times C^(km)`.  This is the exact unstable extension criterion.

There is a relative `K`-theory criterion in the stable range.  Put

```text
d=alpha r,                 M=km,                 n=dim X.
```

If `0<d<M` and

```text
n <= 2 min(d,M-d),                                      (SR)
```

then `(GE)` extends if and only if

```text
[A tensor E_p] in image(K^0(X)->K^0(Y)),                (K)
```

or, equivalently, its boundary in `K^1(X,Y)` is zero.  The cases `d=0,M`
are the evident constant Grassmannians.  Thus, under `(SR)`, relative
`K`-theory is not merely necessary but is the complete obstruction.

Two sharp dimensional consequences follow.

1. If `dim X<=2`, every prescribed projection field `p` extends: complex
   Grassmannians are connected and simply connected, so obstruction theory
   extends its classifying map over every relative cell of dimension at most
   two.  Hence `B_p` already has a nonzero level-one projection.

2. Let `X=D^3`, `Y=S^2`, and let `p in C(S^2,M_2)` be the Bott rank-one
   projection.  Then `B_p` is projectionless, but `M_2(B_p)` contains a
   nonzero projection.  Its first projection level is exactly two.  At level
   one the Bott map `S^2->Gr_1(C^2)=CP^1` has degree one and cannot extend
   over the ball.  At level two take `a=1-p`; the line bundle
   `E_(1-p) tensor E_p` has first Chern class zero, so its map into
   `Gr_1(C^4)=CP^3` is null-homotopic and extends over `D^3`.

The point-rank arithmetic alone predicts level one in this example.  The
relative Bott class genuinely raises the threshold to two, showing that the
finite-point theorem stops sharply when the constrained set acquires
positive-dimensional topology in ambient dimension three.
