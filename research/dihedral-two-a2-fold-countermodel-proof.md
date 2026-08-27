---
rg: 2
id: dihedral-two-a2-fold-countermodel-proof
kind: route
title: Fold the two mixed A2 words through an order-three dihedral packet
target: two-mixed-a2-words-do-not-control-fold-square
requires:
  - one-mixed-a2-word-does-not-control-fold-square
---

On `C^2`, put

```text
S=[[1,0],[0,-1]],
H=[[-1/2,-sqrt(3)/2],[sqrt(3)/2,-1/2]].                (DTA1)
```

Thus `H` is rotation through `2 pi/3`, while `S` is a reflection.  In
particular

```text
H^3=I,              S^2=I,             SHS=H^(-1).    (DTA2)
```

Define the two root packages by

```text
E_12=E_23=A_12=A_23=I,
B_21=B_32=W_12=W_23=S.                                 (DTA3)
```

All displayed coefficient and root matrices commute with `S`.  Moreover,

```text
A_12=E_12^2,       W_12=E_12B_21E_12,
A_23=E_23^2,       W_23=E_23B_32E_23.                 (DTA4)
```

Since both root slots are the identity, their commutator is the identity and
both mixed chamber relations hold:

```text
W_12E_23W_12^*=[E_12,E_23]=I,
W_23E_12W_23^*=[E_12,E_23]^(-1)=I.                    (DTA5)
```

The dihedral relation in `(DTA2)` gives

```text
HSH^*S=H(SH^(-1)S)=H^2.                               (DTA6)
```

Because the `A` slots are the identity and each `B` slot equals its `W`
slot, both unbalanced closures are this same commutator:

```text
D_12=D_23=HSH^*S=H^2.                                 (DTA7)
```

It follows from `H^3=I` that

```text
D_12D_23=H^4=H,
R_tor=H^*D_12D_23=I.                                  (DTA8)
```

Finally the fold itself is `V=H^2`, so `V^2=H^4=H`.  The normalized trace of
a planar rotation is its cosine, and hence

```text
Re tr(V^2)=Re tr(H)=cos(2 pi/3)=-1/2,
||V^2-I||_2^2=2-2 Re tr(V^2)=3.                       (DTA9)
```

The two-projection identity gives the remaining assertion:

```text
tr(QPQ-(QPQ)^2)=(1/16)(1-Re tr(V^2))=3/32.            (DTA10)
```

Every equation in the two-word local interface is therefore exact, while
the fold square remains uniformly nontrivial.

