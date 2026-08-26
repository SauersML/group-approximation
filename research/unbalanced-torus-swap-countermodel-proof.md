---
rg: 2
id: unbalanced-torus-swap-countermodel-proof
kind: route
title: Realize the unbalanced torus closure by a diagonal Mach--Zehnder factorization
target: unbalanced-torus-and-swap-commutation-do-not-control-fold-square
requires:
  - two-torus-closures-detect-denominator-multiplicity
---

Put

```text
Z = [[1,0],[0,-1]],             X = [[0,1],[1,0]],
F = 2^(-1/2)(X+Z),              zeta=exp(pi i/4),
D = diag(1,i).
```

Take

```text
S=Z,                  H=F,
A_12=B_21=D,          W_12=Z,
A_23=zeta^(-1)Z,      B_32=I,       W_23=A_23.          (USP1)
```

All six coefficient matrices are diagonal, so they commute with `S`.  The
elementary two-by-two multiplication

```text
D F D F D = zeta F                                    (USP2)
```

gives

```text
D_12=D F D F D Z,
D_23=A_23,
D_12D_23=F=H,
R_tor=H^*D_12D_23=I.                                  (USP3)
```

For the middle equality, note that

```text
D^*A_23=diag(zeta^(-1),zeta),
```

so `(USP2)` is equivalently

```text
D F D F D^* A_23=F.
```

Thus every equality in `(UTS1)` is exact.  On the other hand `FZF=X`, and
hence

```text
V=HSH^*S=XZ,              V^2=-I.                     (USP4)
```

This proves the first two assertions in `(UTS2)`.  The standard two-projection
identity gives

```text
tr(QPQ-(QPQ)^2)=(1/16)(1-Re tr(V^2))=1/8,             (USP5)
```

proving the last assertion.

The two displayed rank-one packages are internally consistent.  Put

```text
E_12=diag(1,zeta),
E_23=diag(exp(-pi i/8),exp(3pi i/8)).
```

Then direct multiplication gives

```text
E_12^2=A_12,              E_12 B_21 E_12=W_12,
E_23^2=A_23,              E_23 B_32 E_23=W_23.         (USP6)
```

Thus both identities `x_ij(2)=x_ij(1)^2` and both displayed Weyl-word
definitions are exact in the packet.

For comparison, the standard mixed `A_2` identity is already visible.  With
the commutator convention `[a,b]=aba^(-1)b^(-1)`, elimination of `x_13(1)`
from

```text
w_12 x_23(1)w_12^(-1)=x_13(1),
[x_12(1),x_23(1)]=x_13(1)
```

gives

```text
W_12 E_23 W_12^*=[E_12,E_23].                          (USP7)
```

In the packet the left side is `E_23` and the right side is `I`.  Its squared
normalized Hilbert--Schmidt defect is therefore

```text
||E_23-I||_2^2=2-cos(pi/8)-cos(3pi/8)>0.               (USP8)
```

This computes one exact mixed word which the local countermodel omits; it
does not assert that this one defect controls the fold square in all finite
matrix assignments.

There is no conflict with exact arithmetic co-density.  The matrices in
`(USP1)` do not satisfy all omitted lattice relations making the two displayed
rank-one packages part of one exact `SL_3(Z)` representation.  The example
therefore isolates further lattice-word consistency--with joint `A_2`
incidence the first surviving candidate after the existing rank-one
firewalls--as an indispensable input to any continuation from the unbalanced
torus identity to fold-square rigidity.
