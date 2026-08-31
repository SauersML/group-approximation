---
rg: 2
id: three-dimensional-qt-coefficient-algebra-proof
kind: route
title: Compute the eight-element Q-QT algebra and absorb all long-router sign words
target: g2-conditioned-jacobson-sign-envelope-is-finite
requires:
  - jacobson-sign-polar-ranks-are-five-over-72-and-one-over-16
  - qutrit-two-scalar-routers-leave-head-packet-finite
---

## The coefficient algebra

Work in

```text
J=F_2<S,T | TS=1>,             Q=1-ST,             A=QT.
```

The one-sided inverse relation gives

```text
Q^2=(1-ST)^2=1+STST=1+ST=Q,
TQ=T-TST=T-(TS)T=0.                                    (GQP1)
```

It follows immediately that

```text
QA=Q^2T=A,
AQ=QTQ=0,
A^2=QTQT=0.                                             (GQP2)
```

Therefore the `F_2`-span of `1,Q,A` is a unital subalgebra and
contains the generators `Q,A`.

The three displayed elements are linearly independent. To see this
without invoking a normal-form theorem, represent `J` on the
countable `F_2`-space with basis `v_0,v_1,...`. Let

```text
S v_i=v_(i+1),
T v_0=0,                    T v_(i+1)=v_i.
```

Then `TS=1`, while `Q` is the projection onto `F_2v_0` and
`A=QT` sends `v_1` to `v_0` and kills every other basis vector.
The operators `1,Q,A` are linearly independent. Hence their preimages
in `J` are linearly independent, proving `(GQF1)` and
`(GQF2)`.

## The finite long-router group

The scalar qutrit group `C` and the long router `g_2` are matrices
over `F_2`, hence over `A_QT`. The three sign roots have coefficients

```text
H=x_(c_2,c_1)(Q),
C_1=x_(c_2,c_0)(QT)=x_(c_2,c_0)(A),
W=x_(c_2,c_3)(Q).                                      (GQP3)
```

Thus every generator in `(GQF3)` belongs to
`GL_28(A_QT)`. Since `A_QT` has eight elements, this general linear
group and its subgroup `K_QT` are finite.

The head is nonidentity. In the shift representation above, `Q` is a
nonzero projection, so the elementary matrix
`x_(c_2,c_1)(Q)` is not the identity. Therefore the left regular trace
of `K_QT` has

```text
tau(lambda(H))=0,
||lambda(H)-I||_2^2=2.                                  (GQP4)
```

Restriction of the regular representation of a finite group to its
subgroup `C` is a multiple of the regular representation of `C`.
Hence all nine qutrit Fourier atoms have their canonical normalized
weight `1/9`.

## Absorption of the polar calculation

Every `G_(sigma,tau)`, every qutrit cut, and every word involving
`g_2,H,C_1,W,C` lies in the finite-dimensional complex group algebra
`C[K_QT]`. Polar decompositions and support projections of its elements
remain in that algebra by finite-dimensional functional calculus.
Accordingly one faithful finite regular model evaluates simultaneously:

```text
G_(sigma,tau)R,
supp|G_(sigma,tau)R|,
g_2^j G_(sigma,tau)R,
```

and all source, range, and cross terms formed from them.

The sign subgroup `F_0=<C,H,C_1,W>` is a subgroup of `K_QT`.
The restriction of the regular `K_QT`-module to `F_0` is a multiple
of the regular `F_0`-module. Therefore the normalized polar-support
ranks computed in the sign-rank theorem remain exactly `5/72` and
`1/16` in this larger model.

This proves the firewall. The returned mixed coefficient `QT` is not a
raw negative letter: equations `(GQP1)--(GQP2)` keep it in a finite
three-dimensional algebra. At least one occurrence of `T` or `S`
without the left head factor `Q` is necessary to leave
`GL_28(A_QT)`. The result does not say that every such raw-letter word
collapses the head; it identifies the first coefficient-level gate which
is not already exactly absorbed.
