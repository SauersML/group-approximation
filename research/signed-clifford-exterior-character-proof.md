---
rg: 2
id: signed-clifford-exterior-character-proof
kind: route
title: Identify the Clifford monomial action with the full exterior character
target: signed-clifford-cycle-trace-formula
requires: []
---

Give `C` the orthonormal Clifford monomial basis

```text
c_I=c_(i_1)...c_(i_k),       I={i_1<...<i_k} subset {1,...,2m}.
```

Under the vector-space identification of this basis with the standard basis
of the full exterior algebra, the automorphism induced by `R` acts as

```text
directSum_(k=0)^(2m) exteriorPower^k(R).
```

The signs arising when a permuted Clifford monomial is restored to increasing
order are exactly the alternating signs in the exterior power.  Hence its
ordinary linear trace on the `2^(2m)`-dimensional algebra `C` is

```text
sum_k Tr(exteriorPower^k(R))=det(1+R).                  (SCT4)
```

On the other hand `Ad(V)` on `M_(2^m)` is unitarily equivalent, as a linear
operator on Hilbert--Schmidt space, to `V tensor conjugate(V)`.  Therefore

```text
tr_(2^(2m))(Ad(V))=|tr_(2^m)(V)|^2.                    (SCT5)
```

Combining `(SCT4)` and `(SCT5)`, with the normalization by `2^(2m)`, gives
the first equality in `(SCT1)`.

It remains to calculate the determinant by cycles.  On a cycle `D` of
length `ell` and sign-product `s_D`, the signed cycle block has
characteristic polynomial

```text
t^ell-s_D.
```

Evaluation at `t=-1` gives

```text
det(1+R|D)=1-(-1)^ell s_D.                              (SCT6)
```

Multiplication over the cycles proves the second equality in `(SCT1)`.
Each factor in `(SCT6)` is either zero or two, giving `(SCT2)` and `(SCT3)`.
The phase of `tr(V)` cannot be intrinsic because an implementing unitary is
unique only up to a scalar; its absolute value is exactly determined.
