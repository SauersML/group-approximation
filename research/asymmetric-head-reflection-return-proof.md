---
rg: 2
id: asymmetric-head-reflection-return-proof
kind: route
title: Conjugate one head through the later chain and solve the transported center equations
target: asymmetric-head-reflection-return-erases-deep-flags
requires:
  - four-cell-marked-star-has-an-eighth-head-flag
---

Work additively over `F_2` in the commuting involution packet, writing
`c_i,z_i` for the exponents of `C_i,Z_i`.  Conjugation by a head and its
inverse act by

```text
phi_i: c_i |-> c_i+z_(i+1),
       z_i |-> z_i+c_i+z_(i+1),

psi_i: c_i |-> c_i+z_(i+1),
       z_i |-> z_i+c_i                              (i>=2), (1)
```

and fix the other variables needed below.  The first line for `c_i` also
holds at `i=1`; no `z_1` formula is needed.  These are exactly the
Steinberg conjugations `(1)--(2)` in the four-cell proof.

For the monotone word, descending induction gives

```text
Ad(M_m)(c_j)
 =c_j+z_(j+1)+c_(j+1)+...+c_m+z_(m+1)       (1<=j<=m), (2)
```

whereas the inverse direction gives `c_j |-> c_j+z_(j+1)`.  On the
all-negative center carrier, the latter equations force every
`z_2,...,z_(m+1)` to be zero.  This proves `(AHR2)`.

Let `K_m=H_m...H_2`.  Since

```text
R_m=K_mH_1K_m^(-1),                                  (3)
```

its holonomy is genuinely conjugate to that of `H_1`.  Substitution of
`(1)` into `(3)` gives

```text
Ad(R_m)(c_1)=c_1+c_2+...+c_m+z_2+...+z_(m+1),
Ad(R_m)(c_j)=c_j                              (2<=j<=m+1). (4)
```

The inverse has the same action on the center variables, because
`Ad(H_1)` and `Ad(H_1^(-1))` agree there.  With every `c_j=1`, the first
equation in `(4)` is compatible with `c_1=1` exactly when

```text
z_2+...+z_(m+1)=m+1 mod 2.                            (5)
```

Multiplicatively, `(5)` is `Xi_m=epsilon_m`.  All other center conditions
are automatic.  The conjugated center projections commute with `E_m`, so
the two compression products are exactly their intersection projections.
Pauli balance then proves `(AHR4)`.

For the positive palindrome, the same substitution with `phi_i` on both
sides gives `(4)` in the range direction.  In the inverse direction all
higher contributions cancel and

```text
Ad(P_m^(-1))(c_1)=c_1+c_2+z_2,
Ad(P_m^(-1))(c_j)=c_j                         (2<=j<=m+1). (6)
```

Thus its source condition is `z_2=1`, while its range condition is `(5)`.
This proves `(AHR6)`.

Finally write `H_i=B_(i+1)A_i`.  The two root involutions have central
commutator

```text
[B_(i+1),A_i]=x_(k_(i+1),k_i)(b_(i+1)a_i)=:X_i.
```

Therefore `H_i^2=X_i`.  The root `X_i` is nontrivial and has square one,
so `H_i^4=1`, proving `(AHR7)` and the claimed Coxeter-cancellation fence.
