---
rg: 2
id: source-hecke-projective-square-freedom-proof
kind: route
title: Interpolate between the central tensor Haar unitary and the HNN stable letter
target: source-hecke-data-leave-projective-square-free
requires: []
---

There are two endpoint extensions.

First take

```text
P_c=M bar_tensor L(Z),       T_c=1 tensor lambda_Z(1).
```

Then `T_c` commutes with all of `M`, is Haar over `M`, and

```text
tau(T_c^*u_hT_cu_h^*)=1.                                (SHF3)
```

For the other endpoint let

```text
G=<A,t | [t,C]=1>=A *_C (C times Z),
P_f=L(G),              T_f=lambda_G(t).
```

Britton normal form gives `E_M(T_f^k)=0` for every `k!=0`.  Also `T_f`
commutes with `B`.  Since `h notin C`, the word

```text
t^(-1) h t h^(-1)
```

is nontrivial and reduced, so its canonical trace is zero.  Hence

```text
tau(T_f^*u_hT_fu_h^*)=0.                                (SHF4)
```

Given `s in (0,1)`, put `r=sqrt(s)` and take the weighted direct sum

```text
P_s=P_c direct_sum P_f,       tau_s=r tau_c+(1-r)tau_f,
T_s=T_c direct_sum T_f,
```

embedding `M` diagonally.  The trace-preserving conditional expectation
onto the diagonal copy of `M` is

```text
E_M(x direct_sum y)=r E_M^c(x)+(1-r)E_M^f(y).
```

Thus `(SHF1)` holds, while `(SHF3)--(SHF4)` give

```text
tau_s(T_s^*u_hT_su_h^*)=r,
```

which proves `(SHF2)`.  The source copy of `M`, and hence all scalar Gao
conditional moments and source Hecke correspondences, is diagonal and
unchanged throughout the interpolation.  For `s=0` use `(P_f,T_f)` alone,
and for `s=1` use `(P_c,T_c)` alone, so all traces remain faithful.

Finally `g -> tau(T_s^*u_gT_su_g^*)` is a coefficient of the conjugation
representation on `L^2(P_s)`.  Its modulus square is a coefficient of the
doubled conjugation representation, hence positive definite.  Commutation
of `T_s` with `C` makes it `C`-bi-invariant.  This proves every clause.
