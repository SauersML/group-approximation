---
rg: 2
id: titz-witzel-central-square-lifts-proof
kind: route
title: Compare the involution sandwich with a central square
target: titz-witzel-central-square-lifts-collapse-mark
requires:
  - titz-witzel-sofic-gate-two-generators-four-approximate-relators
---

Set

```text
v=u^2,              h=u e u^(-1),
a=e h e,            c=v a v.                              (1)
```

Both `h` and `a` are involutions: `h` is conjugate to `e`, and `a` is
conjugate to `h`.  Thus

```text
a^2=1.                                                    (2)
```

The element `v` commutes with `u`.  Conjugating the comparison
`v e` versus `e v` by `u` therefore gives

```text
d(vh,hv)=d(ve,ev)=eta.                                    (3)
```

Move `v` successively through the three letters of `a=ehe`.  By
bi-invariance, (3), and the definition of `eta`,

```text
d(va,av)<=d(vehe,evhe)+d(evhe,ehve)+d(ehve,ehev)
          <=3 eta.                                        (4)
```

Two applications of (4) give

```text
d(a v^2,v^2 a)<=6 eta.                                    (5)
```

Now use (1), move the central pair `v^2` past the first `a` with (5), and
then use (2):

```text
d(c^2,u^8)
 =d(v a v^2 a v,v^4)
 <=6 eta.                                                  (6)
```

The triangle inequality with `d(c^2,1)=delta` proves `(TWCS1)`, and its
asymptotic consequences are immediate.

For the advertised voltage lift, write

```text
u(x,0)=(x+alpha,1),       u(x,1)=(x+beta,0),
e(x,0)=(x+gamma,1),       e(x,1)=(x-gamma,0).
```

Then `e^2=1`, while `u^2` is translation by `alpha+beta` on both fibres.
Translations in `A` commute, so `u^2e=eu^2`.  Equation `(TWCS1)` specializes
to `d_H(u^8,1)<=d_H(c^2,1)`, as claimed.
