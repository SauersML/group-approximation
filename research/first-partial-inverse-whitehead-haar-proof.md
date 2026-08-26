---
rg: 2
id: first-partial-inverse-whitehead-haar-proof
kind: route
title: Square the Whitehead block and exhaust its involutive row action by finite subgroups
target: first-partial-inverse-whitehead-face-has-haar-mf-character
requires:
  - lef-implies-operator-mf
---

Write `s=s_0`, `t=t_0`, `p=st`, and `q=1-p=s_1t_1`.  The Leavitt relations
give

```text
ts=1,          p^2=p,          q^2=q,
qs=0,          tq=0,          p+q=1.                 (1)
```

In the elementary group, direct multiplication of the three root matrices
gives

```text
(I+sE_23)(I+tE_32)(I+sE_23)
   =diag(1,W,I_(n-3)),
W=[[q,s],[t,0]].                                      (2)
```

Using `(1)`,

```text
W^2=[[q^2+st,qs],[tq,ts]]=I_2.                        (3)
```

An element of the elementary image of `N` is uniquely determined by its row
vector

```text
(a_2,...,a_n),
```

so the Steinberg-to-elementary projection is injective on `N`.  Conjugation
by `(2)` multiplies the coordinates `(a_2,a_3)` on the right by
`W^(-1)=W`, giving exactly `(PIW1)`; the other coordinates are fixed.  Hence
the image of `<N,omega>` is the split semidirect product `(PIW2)`.  Sending
the possible Steinberg-kernel part of the literal word to the identity is a
valid quotient map and does not identify any nonidentity element of `N`.

Let `F` be a finite subset of `(R,+)^(n-1)`.  If `T` denotes the involution
in `(PIW1)`, then

```text
V=span_(F_2)(F union T(F))
```

is finite-dimensional and `T`-invariant.  Therefore

```text
V semidirect <T>                                      (4)
```

is a finite subgroup containing `F` and the Whitehead actor.  These groups,
as `F` grows, exhaust `(PIW2)`.  Thus `(PIW2)` is locally finite, hence LEF.

Use the left regular representation of `(4)`.  Every nonidentity member of
`V` acts without fixed points, so its normalized trace is zero.  Exhausting
the row module yields the regular character of `(PIW2)`, and its pullback to
`<N,omega>` satisfies `(PIW3)`.  The models are exact on each retained
multiplication table, so their operator-norm multiplicative defect is zero;
`lef-implies-operator-mf` packages them as an MF character.

Finally `q!=0`, and injectivity on `N` makes `x_13(q)` nonidentity in every
finite model after it enters the chosen window.  It is an involution, so its
left regular permutation is a union of two-cycles and has operator-norm
distance two from the identity.
