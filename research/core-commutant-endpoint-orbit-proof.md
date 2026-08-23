---
rg: 2
id: core-commutant-endpoint-orbit-proof
kind: route
title: Conjugate the regular endpoint by a signed core-coset projection
target: congruence-iwahori-endpoint-fiber-contains-core-commutant-orbits
requires: []
---

The first assertion is immediate: if `U` commutes with `lambda(K)`, then
`rho_U=Ad(U)o lambda_G` is a representation with

```text
rho_U(r)=lambda(r),       rho_U(t)=lambda(t),
rho_U(w)=X_U.                                              (CCP1)
```

All defining words therefore vanish exactly.

For the noncommuting relative gauge, let `P` be the diagonal projection of
`ell^2(G)` onto `ell^2(K)` and put

```text
U=I-2P.
```

Left multiplication by `K` preserves `ell^2(K)`, so `U` belongs to
`lambda(K)'`.  Write `W=lambda(w)` and

```text
Q=WPW^*,
```

the projection onto `ell^2(wK)`.  Since `U=U^*=U^(-1)`, the relative gauge
is

```text
c_U=UWUW^*=(I-2P)(I-2Q).                                (CCP2)
```

The first factor commutes with `T=lambda(t)`.  The second does not.  Indeed
`TQT^*` is the projection onto `ell^2(twK)`.  The left cosets `twK` and
`wK` are unequal precisely because

```text
w^(-1)t w notin K:                                      (CCP3)
```

the left side is a nontrivial lower unipotent, whereas
`K=<h(2),u(1)>` is contained in the upper triangular subgroup.  Distinct
left cosets are disjoint, so `TQT^*!=Q`.  From `(CCP2)` and `[P,T]=0`,

```text
[c_U,T]=(I-2P)[I-2Q,T] !=0.                             (CCP4)
```

Both endpoints still have zero defect by `(CCP1)`.  Repeating the finite
regular block by direct sum preserves this exact nonalignment, proving the
claimed matrix-level endpoint-fiber obstruction.
