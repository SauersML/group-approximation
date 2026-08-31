---
rg: 2
id: jacobson-residual-t-root-orthogonality-proof
kind: proof
title: Use the ST sign to flip the S2T residual cut
target: jacobson-residual-t-root-is-orthogonal-transport
requires:
  - binary-jacobson-first-alternating-ts-closure-relation
  - binary-jacobson-native-v4-polar-orbit-leaves-one-residual
  - qutrit-jacobson-residual-has-fixed-polar-gap
---

The live residual is a subprojection of the joint character cut on which

```text
x_13(S^2T)=+1,                x_23(ST)=-1.               (JRO4)
```

These two root involutions commute because they have the same target
coordinate.

Apply the elementary commutator formula to

```text
u=x_21(T),                    d=x_13(S^2T).
```

It gives

```text
[u,d]=x_23(TS^2T)=x_23(ST)=r,                            (JRO5)
```

because `TS^2=S`. In characteristic two all displayed root elements
are involutions, so `(JRO5)` is equivalent to

```text
u d u=r d.                                               (JRO6)
```

The roots `u=x_21(T)` and `r=x_23(ST)` share their source row and
commute.

Let `xi` lie in the range of `e`. Using `d xi=xi` and
`r xi=-xi`, equation `(JRO6)` gives

```text
d(u xi)=u(r d xi)=-u xi.                                 (JRO7)
```

Thus `u` maps the range of `e` into the negative `d`-eigenspace.
The range of `e` is contained in the positive `d`-eigenspace, proving
`eue=0` and the orthogonality in `(JRO3)`.

Conjugation preserves canonical trace, so
`tau(u e u)=tau(e)=1/32`. The conjugate defining group `uNu` is again
a two-group. Its intersection with the odd qutrit support group, or with
any scalar conjugate of that support group, is trivial. The coefficient
factorization from the qutrit residual theorem therefore gives the same
masses on `u e u` as on `e`.

Finally, the alternating closure relation obtains `u` as the reduced
value of a word which separately contains a `T`-root and
`k=x_31(1)`. Equation `(JRO3)` concerns the compression after that
word has been multiplied and reduced. It does not assert that every
compression of its typed constituents vanishes. Rather, it proves that a
successful continuation must retain those constituents separately; their
noncommuting compression is the only remaining information discarded by
the reduction to `u`.
