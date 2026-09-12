---
rg: 2
id: sl3-dyadic-exact-action-firewall-proof
kind: route
title: Combine SL3 congruence co-density with the Kazhdan orbit-atlas gap
target: sl3-dyadic-building-action-soficity-forces-p-instability
requires:
  - codense-kazhdan-coset-action-forces-permutation-outliers
  - codense-tau-coset-soficity-forces-permutation-instability
---

The two arithmetic inputs are exact.

First, `C=SL_3(Z)` has property `(T)`.  Fix a finite Kazhdan generating set
and constant `kappa>0`.  Hence the restriction of every finite permutation
representation of `A` to `C` has gap at least `kappa` relative to its
`C`-invariant vectors.

Second, every homomorphism

```text
rho : A -> Sym(V)
```

satisfies `rho(C)=rho(A)`.  Indeed, its kernel has finite index.  The
congruence subgroup property for `SL_3(Z[1/2])` puts inside the kernel a
principal congruence subgroup of odd level `m`; reduction modulo `m` is
defined because `2` is invertible modulo `m`.  The integral subgroup
`SL_3(Z)` surjects onto `SL_3(Z/m)`, so it already surjects onto every
quotient through which `rho` factors.  Thus the `C`- and `A`-orbits of `V`
coincide.

Apply `codense-kazhdan-coset-action-forces-permutation-outliers`.  For an
exact finite action, a two-point orbit atlas of error `epsilon` would label
the base coset by one-hot vectors.  The Kazhdan projection makes that label
`C`-invariant up to squared error at most `4 epsilon/kappa^2`; equality of
the finite `C`- and `A`-orbits makes the projection `h`-invariant.  But atlas
injectivity and covariance say that `h` moves the base label to the distinct
label of `h^(-1)C` on at least a `1-2 epsilon` fraction.  Therefore

```text
1 - 2 epsilon <= 8 epsilon/kappa^2,
```

so every exact finite-action atlas has

```text
epsilon >= kappa^2/(2 kappa^2+8).                         (SD2)
```

The flexible version follows from
`codense-tau-coset-soficity-forces-permutation-instability`: if a sofic
orbit approximation could be corrected after `o(|V|)` padding, discard the
padding and the points on which the Kazhdan generators or `h` changed.  The
same calculation has error tending to zero, contradicting `(SD2)`.  This
proves `(SD1)`.

