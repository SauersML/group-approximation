---
rg: 2
id: separate-d8-carrier-gap-proof
kind: route
title: Round conditional expectations and telescope the D8 holonomy
target: separate-d8-carriers-cannot-recover-in-commuting-descendants
requires: []
---

Let `a=E_A(F)`.  Since conditional expectation is the `L^2` orthogonal
projection and `F` is a projection,

```text
tau(a-a^2)=||F-a||_2^2.
```

For `P=1_[1/2,1](a)`, the pointwise inequality
`|1_[1/2,1](t)-t|^2<=t(1-t)` and Pythagoras give

```text
||F-P||_2<=sqrt(2)dist_2(F,A).                         (1)
```

The same construction gives `Q in B` with
`||G-Q||_2<=sqrt(2)dist_2(G,B)`.  Because `A` and `B` commute, so do
`P,Q`; their reflection commutator is the identity.  Telescope the four
reflection factors and use unitary invariance:

```text
h(F,G)<=2||R_F-R_P||_2+2||R_G-R_Q||_2
       =4||F-P||_2+4||G-Q||_2.
```

Substitution of `(1)` proves the estimate.  For the atlas carriers,
`h^2=1/2`; hence `dist(F,A)+dist(G,B)>=1/8` (a weaker rounded constant than
the sharp quotient, retained uniformly).  An approximate returned
holonomy contributes additively by the same telescoping argument.
