---
rg: 2
id: exact-bs-core-stratum-normal-form-proof
kind: route
title: Align the finite-order root spectrally and identify the remaining implementer ratio
target: exact-bs-core-strata-have-conjugation-commutant-normal-form
requires:
  - optimized-core-one-sided-normal-slice-is-exactly-coercive
---

Equality of the `N`th-root multiplicity vectors gives a unitary `z` with
`T_1=zT_0z^(-1)`.  Put

```text
R_z=zR_0z^(-1),             q=R_1R_z^(-1).            (BCP1)
```

Both `R_z` and `R_1` implement `T_1 -> T_1^4`.  Therefore

```text
qT_1^4q^(-1)
 =R_1(R_z^(-1)T_1^4R_z)R_1^(-1)
 =R_1T_1R_1^(-1)=T_1^4.                              (BCP2)
```

Because `T_1^N=1` and `gcd(4,N)=1`, `T_1` is an integral power of `T_1^4`.
Equation `(BCP2)` consequently gives `[q,T_1]=1`, proving `(BCS2)`.

Conversely, if `[q,T_1]=1`, then

```text
(qR_z)T_1(qR_z)^(-1)=qT_1^4q^(-1)=T_1^4,
```

so `(qR_z,T_1)` is exact.  This proves the global stratum normal form.

Finally `(X_1,R_z,T_1)` is the common conjugate by `z` of the baseline exact
endpoint.  The supplied core is `(qR_z,T_1)` with `q in {T_1}'`, so
`optimized-core-one-sided-normal-slice-is-exactly-coercive` applies verbatim
and gives `(BCS3)`.

