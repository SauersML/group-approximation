---
rg: 2
id: closed-a2-loop-fold-countermodel-proof
kind: route
title: Tensor an odd congruence A2 packet with a two-sheet torus gauge
target: closed-a2-loop-still-leaves-swap-fold-free
requires:
  - one-mixed-a2-word-does-not-control-fold-square
  - two-torus-closures-detect-denominator-multiplicity
---

Let `m>=3` be odd, `Q=SL_3(Z/mZ)`, and let `rho` be the left regular
representation of `Q`.  Since `2` is invertible modulo `m`, reduction
modulo `m` extends `rho` from `SL_3(Z)` to
`A=SL_3(Z[1/2])`.  On its representation space put

```text
e_12=rho(x_12(1)),             e_23=rho(x_23(1)),
a_12=rho(x_12(2))=e_12^2,     a_23=rho(x_23(2))=e_23^2,
b_21=rho(x_21(-1)),            b_32=rho(x_32(-1)),
w_12=e_12 b_21 e_12,           w_23=e_23 b_32 e_23,
K=rho(h).                                                   (CAP1)
```

The standard `A_2` identities give

```text
w_12 e_23 w_12^*=[e_12,e_23]=w_23^*e_12w_23.           (CAP2)
```

Let `X,Z` be the Pauli matrices and set

```text
theta=2 pi/3,              H_0=exp(i theta X),
V=H_0 Z H_0^* Z.                                        (CAP3)
```

Conjugating `Z` by the `X`-rotation gives

```text
V=exp(2 i theta X),        V^2=exp(4 i theta X)=H_0.    (CAP4)
```

The last equality uses `3 theta=2 pi`.

On `C^2 tensor l^2(Q)` define

```text
S=Z tensor 1,                         H=H_0 tensor K,

E_12=1 tensor e_12,                   A_12=1 tensor a_12,
B_21=Z tensor b_21,                   W_12=Z tensor w_12,

E_23=1 tensor e_23,                   A_23=1 tensor a_23,
B_32=Z tensor b_32,                   W_23=Z tensor w_23. (CAP5)
```

Every displayed coefficient commutes with `S`.  Equations `(CAP1)` give
the two rank-one packages:

```text
E_12^2=A_12,      E_12B_21E_12=W_12,
E_23^2=A_23,      E_23B_32E_23=W_23.                   (CAP6)
```

The sheet signs cancel from conjugation and from the commutator, so `(CAP2)`
gives the closed loop exactly:

```text
W_12E_23W_12^*=1 tensor [e_12,e_23]
                  =[E_12,E_23]
                  =W_23^*E_12W_23.                    (CAP7)
```

Now evaluate the two torus closures.  Their sheet factors are both `V`,
while their congruence factors are the genuine denominator tori from
`(TTC3)`:

```text
D_12=V tensor rho(diag(2,2^(-1),1)),
D_23=V tensor rho(diag(1,2,2^(-1))).                   (CAP8)
```

Indeed `(CAP8)` follows by inserting `(CAP5)` in `(TTC2)`; the two `Z`
factors occur in `B_ji` and `W_ij^*`, producing
`H_0 Z H_0^*Z=V`, and the remaining factor is exactly the evaluation under
`rho`.  Equations `(TTC3)` and `(CAP4)` therefore yield

```text
D_12D_23=V^2 tensor K=H_0 tensor K=H,                  (CAP9)
```

so `R_tor=H^*D_12D_23=1`.

Finally the congruence factor cancels from the fold:

```text
F=HSH^*S=V tensor 1,             F^2=H_0 tensor 1.     (CAP10)
```

The normalized trace of `H_0` is `cos(theta)=-1/2`, whence

```text
Re tr(F^2)=-1/2,
||F^2-1||_2^2=2-2 Re tr(F^2)=3.                        (CAP11)
```

The standard two-projection identity gives the last value in `(CAL3)`:

```text
tr(QPQ-(QPQ)^2)=(1/16)(1-Re tr(F^2))=3/32.             (CAP12)
```

The construction is finite and exact.  Its failure to extend to the full
lattice is also explicit: the two negative simple-root and Weyl slots carry
the sheet sign `Z`, while the positive-root slots do not.  Since
`SL_3(Z)` has no such sign character, some further lattice relation must
detect it.  Neither torus closure nor either shortest highest-root return
does.
