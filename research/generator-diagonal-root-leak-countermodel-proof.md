---
rg: 2
id: generator-diagonal-root-leak-countermodel-proof
kind: route
title: Put the skew leaking root inside a fully central unbalanced torus packet
target: generator-diagonal-does-not-couple-to-root-leak
requires: []
---

Put

```text
Z=[[1,0],[0,-1]],       X=[[0,1],[1,0]],
F=2^(-1/2)(X+Z),        D=diag(1,i),
E=exp(i*pi/4) Z.
```

Write `Z'` for `Z` in a second copy of `M_2`.  On `M_2 tensor M_2` set

```text
T=Z tensor I,                    H=F tensor I,
A_12=I tensor I,                 W_12=I tensor iZ',
A_23=D tensor I,                 W_23=E tensor I,
B_21=Z tensor iZ',               B_32=D tensor I.       (GDC1)
```

All six displayed lattice matrices commute with `T`, so the whole
generator diagonal `(GDR2)` is `T`-central.  The two torus factors are

```text
D_12=A_12(HB_21H*)A_12W_12*=X tensor I.                 (GDC2)
```

For the second factor, write

```text
D=(1+i)I/2+(1-i)Z/2.
```

Since `FZF=X`, direct multiplication gives

```text
D(FDF)D=exp(i*pi/4)F,
D_23=A_23(HB_32H*)A_23W_23*=FZ tensor I.                (GDC3)
```

The identity `XF=FZ` now yields

```text
D_12D_23=XFZ tensor I=F tensor I=H,                    (GDC4)
```

so the unbalanced relator defect is zero.  Also

```text
tr_4([T,H])=tr_2(ZFZF)=0.                               (GDC5)
```

Finally `T_1=H^*TH=X tensor I`, whence

```text
T_1B_21T_1^*=-B_21,
||T_1B_21T_1^*-B_21||_2=2.                              (GDC6)
```

This proves `(GDR1)`.

It remains to calculate the distinguished support function.  Let

```text
K=C_2*F_5=<r,u_2,...,u_6 | r^2=1>,
```

index `r` by `B_21`, and index the five free generators by the other five
matrices in `(GDC1)`.  Let `x=(X_s)_(s in S_0)` be this assignment.  For
every ucp map `Phi:C^*(K)->M_4`, `Phi(r)` is self-adjoint.  Since
`B_21^*=-B_21`, cyclicity of the trace gives

```text
Re tr_4(B_21^* Phi(r))=0.                               (GDC7)
```

Every other `Phi(u_j)` is a contraction, so

```text
Re sum_(s in S_0) tr_4(X_s^*Phi(u_s)) <=5.             (GDC8)
```

Equality is attained: take two representations which send `r` to `I` and
`-I`, respectively, send every free generator to its assigned `X_s`, and
average them.  The resulting ucp map sends `r` to zero and every `u_j` to
`X_j`.  Therefore, for `C_s=X_s/sqrt(6)`,

```text
h_4(C)=5/sqrt(6),
Re sum_s tr_4(C_s^*X_s)=sqrt(6),
Delta(C;X)=1/sqrt(6).                                  (GDC9)
```

Lastly `W^*(T)=span{I,Z} tensor I`, whereas the normalized trace of `iZ'`
is zero.  Hence

```text
E_(W^*(T))(B_21)=E_(W^*(T))(Z tensor iZ')=0,            (GDC10)
```

which proves `(GDR4)` and the claim.
