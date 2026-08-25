---
rg: 2
id: seventeen-root-star-overlap-proof
kind: route
title: Combine the quarter floor with Weyl two-transitivity and a second moment
target: seventeen-root-star-has-marked-triple-overlap
requires:
  - commuting-double-commutator-has-direct-mark-overlap
---

All roots `x_(i,2)(q)` have the same column, so their involutions commute.
Their indices avoid the marked indices `1,3`, so they also commute with
`x_13(q)`.  Hence

```text
E_i=P Q_i
```

are commuting projections supported on `P`.

Permutations of the seventeen indices `4,...,20`, fixing `1,2,3`, lift to
Weyl words.  They fix `x_13(q)` and act two-transitively on the ordered roots
`x_(i,2)(q)`.  Traciality therefore gives constants `a,t` such that

```text
tau(E_i)=a,
tau(E_iE_j)=t                       for every i!=j.     (SRP1)
```

Each `x_(i,2)(q)` is globally Weyl-conjugate to `x_13(q)`, so
`tau(Q_i)=tau(P)`.  Apply
`commuting-double-commutator-has-direct-mark-overlap` in the disjoint root
rectangle to get

```text
a=tau(PQ_i)>=tau(P)/4.                                (SRP2)
```

Put `X=sum_(i=4)^20 E_i`.  Since `X=PXP`, tracial Cauchy--Schwarz gives

```text
tau(X^2)>=tau(X)^2/tau(P).
```

Using `(SRP1)` on the seventeen diagonal and `17*16=272` ordered
off-diagonal terms,

```text
17a+272t >= 289a^2/tau(P).                             (SRP3)
```

The right side after solving for `t` is increasing for
`a>=tau(P)/4`.  Substitution of `(SRP2)` yields

```text
t >= [(289/16)-(17/4)]tau(P)/272
  = 221 tau(P)/4352
  = 13 tau(P)/256,                                     (SRP4)
```

which is `(SRS2)`.  There are only seventeen fixed roots and finitely many
fixed Weyl words, so rounding and fixed-word telescoping make all equalities
`o(1)`-accurate in an operator-norm microstate, proving the robust form.
