---
rg: 2
id: one-mixed-a2-fold-countermodel-proof
kind: route
title: Repair the first mixed A2 word on an internal Pauli qubit
target: one-mixed-a2-word-does-not-control-fold-square
requires:
  - unbalanced-torus-and-swap-commutation-do-not-control-fold-square
---

Let `X,Y,Z` be the Pauli matrices and put

```text
R=diag(1,i),
H_0=(1/2)Z+(sqrt(3)/2)X,
x=Z,                 y=(X+Z)/sqrt(2),
w=(1/2)X+(1/sqrt(2))Y+(1/2)Z.                         (OMP1)
```

The three matrices `H_0,y,w` are self-adjoint involutions.  The Bloch vectors
of `y` and `w` are respectively

```text
n=(1/sqrt(2),0,1/sqrt(2)),
q=(1/2,1/sqrt(2),1/2)=(n+e_y)/sqrt(2).
```

Conjugation by the reflection `w=q dot (X,Y,Z)` sends `n` to `e_y`.
Consequently

```text
w y w=Y.
```

Also, direct Pauli multiplication gives

```text
[x,y]=x y x y=iY.                                    (OMP2)
```

Set

```text
b=xwx,                     K=w^*b=wxwx.               (OMP3)
```

All of `b,K` are unitary, and the definition of `K` gives the useful exact
cancellation

```text
K b K^* w^*=K.                                        (OMP4)
```

Indeed, `K^*=b^*w`, so the left side is
`w^* b^2 b^* w w^*=w^*b=K`.

Work on `C^2 tensor C^2`, with the first factor called the sheet factor, and
define

```text
S    =Z tensor I,                 H    =H_0 tensor K,

E_12 =R tensor x,                 A_12 =Z tensor I,
B_21 =Z tensor b,                 W_12 =I tensor w,

E_23 =i I tensor y,               A_23 =-I tensor I,
B_32 =I tensor I,                 W_23 =-I tensor I.   (OMP5)
```

Every displayed coefficient and root slot commutes with `S`, and `S^2=1`,
`H^*H=1`.  Since `R^2=Z`, `x^2=y^2=1`, `RZR=1`, and
`xbx=w`, equations `(OMA2)` follow immediately:

```text
E_12^2=A_12,       E_12B_21E_12=W_12,
E_23^2=A_23,       E_23B_32E_23=W_23.                 (OMP6)
```

The scalar and sheet factors cancel from the commutator in the mixed word.
Using `(OMP2)` and `wyw=Y`,

```text
W_12E_23W_12^*=i I tensor Y
                  =[E_12,E_23].                       (OMP7)
```

It remains to check the unbalanced torus word.  With
`H_0=(1/2)Z+(sqrt(3)/2)X`, Pauli multiplication gives

```text
Z H_0 Z H_0 Z=-H_0.                                   (OMP8)
```

Equations `(OMP4)` and `(OMP8)` now give

```text
D_12=(-H_0) tensor K,
D_23=-I tensor I,
D_12D_23=H_0 tensor K=H.                              (OMP9)
```

Therefore `R_tor=H^*D_12D_23=I`, proving every equality in
`(OMA1)--(OMA3)`.

Finally the internal factor cancels from the fold:

```text
V=HSH^*S=(H_0 Z H_0 Z) tensor I
 =(-1/2 I-i sqrt(3)/2 Y) tensor I.                    (OMP10)
```

Hence

```text
V^2=(-1/2 I+i sqrt(3)/2 Y) tensor I,
Re tr(V^2)=-1/2,
||V^2-I||_2^2=2-2 Re tr(V^2)=3.                       (OMP11)
```

The standard two-projection identity then yields

```text
tr(QPQ-(QPQ)^2)=(1/16)(1-Re tr(V^2))=3/32.            (OMP12)
```

Thus the fold square remains uniformly nontrivial although the first mixed
`A_2` word and every earlier local input are exact.

