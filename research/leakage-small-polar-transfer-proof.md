---
rg: 2
id: leakage-small-polar-transfer-proof
kind: route
title: Apply property T to the zero-extended corner and cancel the rank normalization
target: leakage-small-polar-compressions-obey-projective-transfer
requires:
  - exact-projective-codensity-has-a-uniform-trace-square-gap
---

Write `D=dim(H)` and use normalized Hilbert--Schmidt norm on `PH` unless a
subscript `H` is shown.  If `T_s=P pi(s)P`, the polar estimate gives

```text
||T_s-rho(s)||_(2,PH)^2
 <= ||(1-P)pi(s)P||_HS^2/m.                              (LPC3)
```

On each singular value `0<=a<=1`, `(1-a)^2<=1-a^2`; arbitrary unitary
completion on the zero singular space has exactly the allowed unit cost.
Since `S_A` is symmetric, `(LPC1)` also controls incoming leakage and the
normalized commutators `[P,pi(s)]`.  Telescoping along the finitely many
fixed presentation relators, followed by `(LPC3)`, shows that `rho` has
presentation defect at most `C_0 sqrt(ell)`.

Put

```text
q=sum_(c in S_C)(1-|tr_PH([U,rho(c)])|^2).
```

The fixed perfectness calculation `(PTS4)` applied to `rho` removes source
scalar phases and gives

```text
max_(c in S_C)||U rho(c)-rho(c)U||_(2,PH)
 <= C_1(sqrt(q)+sqrt(ell)).                               (LPC4)
```

Extend `U` by zero: `V=PUP in M_D`.  Equations `(LPC3)--(LPC4)` and the two
off-diagonal leakage blocks imply

```text
max_(c in S_C)||Vpi(c)-pi(c)V||_(2,H)
 <= sqrt(m/D) C_2(sqrt(q)+sqrt(ell)).                    (LPC5)
```

Apply property `(T)` of `C` to its exact conjugation representation on
`M_D`.  The vector `V` is within the right side of `(LPC5)`, divided by the
fixed Kazhdan constant, of `pi(C)'`.  Finite-dimensional co-density gives
`pi(C)'=pi(A)'`.  Therefore

```text
||Vpi(h)-pi(h)V||_(2,H)
 <= sqrt(m/D) C_3(sqrt(q)+sqrt(ell)).                    (LPC6)
```

Compress back to `PH`.  Dividing by `sqrt(m/D)` exactly cancels the rank
factor, regardless of codimension.  Comparing `Ppi(h)P` with its polar
correction by `(LPC3)` yields

```text
||U rho(h)-rho(h)U||_(2,PH)
 <= C_4(sqrt(q)+sqrt(ell)).                              (LPC7)
```

The additive commutator norm equals `||[U,rho(h)]-1||_2`, and
`1-|tr(W)|^2<=||W-1||_2^2` for a unitary `W`.  Squaring `(LPC7)` proves
`(LPC2)` after enlarging the constant.

