---
rg: 2
id: binary-jacobson-native-clifford-tower-proof
kind: route
title: Pair opposite finitary matrix units and place the tower inside the amenable symbol kernel
target: binary-jacobson-head-sector-has-native-clifford-tower
requires:
  - binary-jacobson-monomial-symbol-preimage-is-marked-mf
---

On the standard one-sided Jacobson module, the finitary matrix units are

```text
E_ab=S^a Q T^b.                                         (1)
```

Thus `Q T^i=E_(0i)` and `S^j Q=E_(j0)`.  Matrix-unit
multiplication gives

```text
(Q T^i)(S^j Q)=E_(0i)E_(j0)=[i=j]E_(00)=[i=j]Q.        (2)
```

Equivalently, `(2)` follows directly from `TS=1`, `QS=0`, and `TQ=0` by
canceling the shorter of `T^i,S^j`.

The Steinberg relation through index `2` now gives

```text
[x_12(QT^i),x_23(S^jQ)]=x_13([i=j]Q)=w^[i=j].          (3)
```

Roots in one common row commute and roots in one common column commute, so
the remaining relations in `(JCT2)` follow.  The central root `x_13(Q)`
commutes with both families.  All generators are involutions in
characteristic two.

Reordering with `(3)` puts every packet element in the form

```text
w^c product_i X_i^(a_i) product_i Z_i^(b_i).            (4)
```

This normal form is unique in the natural elementary-matrix representation:
the coefficients `E_(0i)`, `E_(i0)`, and `E_(00)` are linearly independent
in their respective root positions.  Thus `C_N` has order `2^(1+2N)` and is
the asserted extraspecial group, not merely a quotient of it.

On the `w=-1` sector, `(3)` says that the `N` pairs are anticommuting within
each pair and commuting across different pairs.  Their complex star-algebra
is the tensor product of `N` copies of `M_2(C)`, hence `M_(2^N)(C)`.  Its
finite-dimensional representations are amplifications of the defining one,
which proves the divisibility assertion.

Each coefficient in `(JCT1)` lies in the finitary ideal, so every root lies
in the finitary kernel `L`; this proves the first inclusion in `(JCT4)`.
The second is part of the definition of the monomial-symbol preimage.  The
prerequisite proves that `K` is amenable and has a faithful operator-MF model
with `w!=1`.  Restriction of that model proves the marked-MF firewall for the
whole Clifford tower and all monomial transports.
