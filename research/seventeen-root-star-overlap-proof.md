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
Weyl words.  They fix `x_13(q)` and act `k`-transitively on ordered distinct
roots for every `k<=17`.  Traciality therefore makes the trace of
`P Q_(i_1)...Q_(i_k)` depend only on `k`; call it `t_k`, and put

```text
tau(E_i)=a.                                               (SRP1)
```

Each `x_(i,2)(q)` is globally Weyl-conjugate to `x_13(q)`, so
`tau(Q_i)=tau(P)`.  Apply
`commuting-double-commutator-has-direct-mark-overlap` in the disjoint root
rectangle to get

```text
a=tau(PQ_i)>=tau(P)/4.                                (SRP2)
```

Put `N=sum_(i=4)^20 E_i`.  The commuting projections make `N` an
integer-valued operator on `PH`, with

```text
tau(N)=17a >= (17/4)tau(P).                             (SRP3)
```

For `2<=k<=5`, functional calculus and `k`-transitivity give

```text
tau(binomial(N,k))=binomial(17,k)t_k.                  (SRP4)
```

On every integer `n>=0`, the following supporting-line inequalities hold:

```text
binomial(n,2)>=4n-10,        binomial(n,3)>=6n-20,
binomial(n,4)>=4n-15,        binomial(n,5)>=n-4.        (SRP5)
```

Apply `(SRP5)` to `N`, use `(SRP3)`, and divide by the corresponding values

```text
binomial(17,2)=136,     binomial(17,3)=680,
binomial(17,4)=2380,    binomial(17,5)=6188.
```

This gives respectively

```text
t_2>=7tau(P)/136,          t_3>=11tau(P)/1360,
t_4>=tau(P)/1190,          t_5>=tau(P)/24752,          (SRP6)
```

which is `(SRS2)`.  There are only seventeen fixed roots and finitely many
fixed Weyl words, so rounding and fixed-word telescoping make all equalities
`o(1)`-accurate in an operator-norm microstate, proving the robust form.
