---
rg: 2
id: binary-jacobson-active-cycle-generation-proof
kind: route
title: Extract S, the head idempotent, and T by conjugating constant roots
target: binary-jacobson-one-balanced-shift-and-constant-cycle-generate-e3
requires: []
artifacts:
  - notes/PROPERTY_T_FREE_MF_ATTEMPT_2026-08-26.md
---

The Steinberg commutator relations applied to `(J3G1)` give

```text
[x_12(1),x_23(1)]=x_13(1),
[x_23(1),x_31(1)]=x_21(1),
[x_31(1),x_12(1)]=x_32(1).                             (J3GP1)
```

Hence `C` contains every constant root and therefore the constant group
`EL_3(F_2)`.  In particular it contains the Weyl swap

```text
w_12=x_12(1)x_21(1)x_12(1).
```

The elementary factorization used in the balanced-shift calculation gives

```text
h:=a_12 w_12
  =x_12(S)x_21(T)x_12(S)
  =[[Q,S,0],[T,0,0],[0,0,1]].                          (J3GP2)
```

The Jacobson relations imply

```text
h^2=1                                                   (J3GP3)
```

because `Q^2=Q`, `Q S=0`, `T Q=0`, `ST+Q=1`, and `TS=1`.
Conjugating three constant roots by this literal involution yields

```text
h x_23(1) h = x_13(S),
h x_31(1) h = x_31(Q)x_32(S),
h x_13(1) h = x_13(Q)x_23(T).                          (J3GP4)
```

These formulas follow by left multiplication of coefficient columns and
right multiplication of coefficient rows by the displayed `2 x 2` block of
`h`.  The factors on each right-hand side commute.

Constant Weyl conjugation moves a coefficient root to any other off-diagonal
position (there are no signs in characteristic two).  The first equation of
`(J3GP4)` therefore gives every `x_ij(S)`.  In the second equation the factor
`x_32(S)` is now known, so it can be cancelled to obtain `x_31(Q)` and hence
every `x_ij(Q)`.  In the third equation the known `x_13(Q)` can be cancelled
to obtain `x_23(T)` and hence every `x_ij(T)`.

Let

```text
R_0={r in J : x_ij(r) belongs to <a_12,C> for every i != j}.
```

Root addition makes `R_0` additively closed.  Given `r,s in R_0` and
`i != j`, choose the third index `k`; then

```text
[x_ik(r),x_kj(s)]=x_ij(rs),                            (J3GP5)
```

so `R_0` is multiplicatively closed.  The preceding extraction shows that
`1,S,T in R_0`.  Since those elements generate `J` as a ring, `R_0=J`.
Thus the generated subgroup contains every elementary generator of
`EL_3(J)`.  The reverse containment is immediate from the definitions,
proving `(J3G2)`.
