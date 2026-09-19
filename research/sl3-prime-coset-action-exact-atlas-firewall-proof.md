---
rg: 2
id: sl3-prime-coset-action-exact-atlas-firewall-proof
kind: route
title: Apply prime-uniform permutation co-density to the Kazhdan orbit-atlas gap
target: sl3-prime-coset-action-exact-atlas-firewall
requires:
  - sl3-prime-permutation-codensity
  - codense-kazhdan-coset-action-forces-permutation-outliers
  - codense-tau-coset-soficity-forces-permutation-instability
  - gkp-sofic-action-toolkit
  - sl3-finite-building-quotients-forget-arithmetic-labels
  - arithmetic-integral-subgroup-is-incompressible
---

The pair `Lambda<Gamma` meets the two hypotheses of
`codense-kazhdan-coset-action-forces-permutation-outliers`.

First, `Lambda=SL_3(Z)` has property `(T)`, so its fixed finite Kazhdan set
has a uniform gap `kappa` in every permutation representation, relative to
the invariant vectors.  Second, `sl3-prime-permutation-codensity` gives

```text
rho(Lambda)=rho(Gamma)
```

for every exact finite action `rho` of `Gamma`.  The abstract orbit-atlas
theorem therefore gives `(PAF1)`.  Applying
`codense-tau-coset-soficity-forces-permutation-instability` gives the
flexible statement: deleting vanishing padding and the points on which the
finitely many generators changed would otherwise transfer a sofic atlas to
an exact one with error tending to zero, contradicting `(PAF1)`.

The criteria audit is then formal.  `gkp-sofic-action-toolkit` proves
soficity for `G curvearrowright G/N` when `G` is sofic and `N` is locally
finite; here `N=Lambda` is not locally finite.  The same verified source
says that all actions of sofic groups were not known to be sofic and that
even amenable stabilizers were not settled there; our stabilizer is
nonamenable anyway.  Prime-uniform co-density gives the failure of subgroup
separability and of all finite-quotient constructions.  Finally the
incompressibility theorem rules out importing the later Kun--Thom negative
criterion.  The building-label theorem identifies the remaining
construction problem as coherent approximate deck-cocycle rounding, rather
than an exact quotient action.
