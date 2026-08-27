---
rg: 2
id: schur-violation-density-gives-contraction
kind: claim
title: Positive violation density turns Schur child branching into a strict backward contraction
distinct_from:
  contractive-computation-ladder: that sums a strict scalar recurrence once supplied; this derives the recurrence from violation density and the one-versus-two Schur child branching law.
  coherent-sequential-schur-tape-payment: that orients the predicate toward satisfying Fanizza propagation and must charge inactive sectors; this orients the predicate toward violation, so every sector reproduces and violations supply the surplus.
---

Let `a_n,v_n,c_n>=0`, let `beta>0`, and suppose

```text
v_n >= beta a_n-delta_n,                              (SVG1)
c_n = a_n+v_n,                                        (SVG2)
a_(n+1) >= c_n-eta_n.                                 (SVG3)
```

Then, with `lambda=(1+beta)^(-1)<1`,

```text
a_n <= lambda a_(n+1)+lambda(delta_n+eta_n).          (SVG4)
```

Consequently, if `a_n` is uniformly bounded and

```text
delta_n+eta_n <= C(n+1)^k sqrt(E),                    (SVG5)
```

then `contractive-computation-ladder` gives

```text
a_0 <= C' sqrt(E),                                    (SVG6)
```

where `C'` depends only on `beta,C,k`, not on matrix dimension.

For a Schur--Clifford violation packet, `(SVG2)` is exactly the child identity:
every satisfying packet simple restricts to one child simple, while every
violating simple restricts to two. Thus the child total is the old total plus
the violating total. Unlike the satisfying-oriented half-return, this
accounting has no inactive sector.
