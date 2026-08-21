---
rg: 2
id: free-cone-shift-clifford-tail-proof
kind: route
title: Represent the positive free monoid by controlled-Z cone products
target: free-cone-shift-finitely-wordizes-recursive-clifford-tails
requires: []
---

Write `u_i=s_i t s_i^(-1)`.  The presentation says that `u_0,u_1`
commute, are involutions, and

```text
t=c u_0u_1.                                               (1)
```

Consequently `(u_0u_1)^2=1`, and right multiplication of `(1)` by
`u_0u_1` gives `t u_0u_1=c`.  Conjugation by `g_x` proves all three
identities in `(FCS3)`.  A conjugate of a defining relator is one cell in
relative area, while `|g_x|=|x|`; this proves the claimed address and
derivation bounds.

For noncollapse, let `K=C^4`, `q=|00>`, and

```text
H=restrictedTensor_(h in F) (K,q).
```

If `A` is any subset of `F`, the formula

```text
D_A(product_h eta_h)=product_h D_h eta_h
```

on elementary tensors is meaningful: only finitely many `eta_h` differ
from `q`, and `Dq=q`.  It defines a unitary involution, with
`D_A D_B=D_(A symmetricDifference B)`.  Let `U_g` permute tensor factors
by left translation.  Then

```text
U_g D_A U_g^*=D_(gA).                                    (2)
```

Take `rho(s_i)=U_(s_i)`, `rho(c)=D_{e}`, and `rho(t)=D_P`.  Freeness gives
the disjoint decomposition

```text
P={e} disjointUnion s_0P disjointUnion s_1P.              (3)
```

Equations `(2)--(3)` imply

```text
D_P=D_{e}D_(s_0P)D_(s_1P),
[D_(s_0P),D_(s_1P)]=1,
```

so `rho` respects `(FCS1)`.  A tensor with local state `|11>` at `e` and
reference state elsewhere is negated by both `rho(c)` and `rho(t)`, proving
that the two designated gates survive.  More generally `(2)` sends their
addressed conjugates to the site `g_x` and cone `g_xP`, respectively, and
conjugating `(3)` gives the exact binary recursion at every address.

