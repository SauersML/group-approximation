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

For the converse on the regular endpoint fiber, finite-group
representations are unitarily equivalent exactly when their characters
agree.  Hence an exact `rho_X` with the regular character has
`rho_X=Ad(V)o lambda_G` for some unitary `V`.  For every `k in K`, agreement
on the fixed core gives

```text
V lambda(k)V^*=rho_X(k)=lambda(k),
```

so `V in lambda(K)'`.  Evaluating at `w` proves that every regular endpoint
is in the displayed orbit.

For the uniformly noncommuting relative gauge, put

```text
s=w^(-1)t w.
```

This is a nontrivial lower unipotent, while
`K=<h(2),u(1)>` lies in the upper triangular subgroup, so `s notin K`.
Partition `G` into the left-`K` orbits `Kg`.  Choose each orbit independently
with probability `1/2` and let `A` be the union of the chosen orbits.  For
every `g`, the orbits `Kg` and `Ks^(-1)g` are distinct: equality would imply
`s^(-1) in K`.  Their two selection bits are therefore independent, and

```text
E |A triangle sA|=|G|/2.                               (CCP2)
```

Fix one choice with `|A triangle sA|>=|G|/2`.  Let `P` be multiplication by
the indicator of `A` on `ell^2(G)` and put

```text
U=I-2P.
```

The set `A` is a union of left-`K` orbits, so `U` belongs to
`lambda(K)'`.  Write `W=lambda(w)` and

```text
Q=WPW^*,
```

the projection onto `ell^2(wA)`.  Since `U=U^*=U^(-1)`, the relative gauge
is

```text
c_U=UWUW^*=(I-2P)(I-2Q).                                (CCP3)
```

The first factor commutes with `T=lambda(t)`.  Moreover `TQT^*` is the
projection onto

```text
t w A=w s A.
```

Consequently normalized counting trace gives

```text
||TQT^*-Q||_2^2=|A triangle sA|/|G|>=1/2.              (CCP4)
```

Using `(CCP3)` and `[P,T]=0`,

```text
[c_U,T]=(I-2P)[I-2Q,T],
||[c_U,T]||_2=2||TQT^*-Q||_2>=sqrt(2).                 (CCP5)
```

Both endpoints still have zero defect by `(CCP1)`.  The lower bound is
independent of `G`, and repeating any finite regular block by direct sum
preserves it.  Thus the obstruction survives both amplification and moving
congruence levels.
