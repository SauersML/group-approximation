---
rg: 2
id: stw83-circle-unitary-order-zero-plus-constants-gap
kind: claim
title: One order-zero colour plus constants stays uniformly away from the circle generator
distinct_from:
  stw83-plateau-buffer-recolouring-hinge: that rules out a block-diagonal whole-corner scheme; this gives a quantitative finite-set obstruction even when the second colour has arbitrary off-diagonal plateau transport.
---

Let `z` be the coordinate unitary in `C(T)`.  There is a universal constant
`delta>0` such that, for every finite-dimensional C*-algebra `F`, every cpc
order-zero map

```text
eta:F -> C(T),
```

every contraction `b in F`, and every scalar `c`, one has

```text
norm(z-c-eta(b)) >= delta.                              (1)
```

Consequently, let `D=M_r(C(T))` and let `e in D` be a constant rank-one
projection.  Suppose

```text
eta^(0):F^(0)->eDe,
eta^(1):F^(1)->D
```

are cpc order-zero maps.  If contractions `b_i in F^(i)` satisfy

```text
e eta^(1)(b_1) e in C e,                                (2)
```

then

```text
norm(z e-eta^(0)(b_0)-eta^(1)(b_1)) >= delta.           (3)
```

Thus allowing the second plateau colour to carry arbitrary off-diagonal
matrix terms is not by itself enough for the relative Brake--Winter
construction.  On the finite set containing `z e`, that colour must also
carry genuinely coefficient-varying information on the rank-one plateau
diagonal.  A scalar diagonal combined with one plateau-supported order-zero
colour has a uniform error floor.
