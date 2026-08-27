---
rg: 2
id: relative-kazhdan-bimodule-circularity-proof
kind: route
title: Evaluate the semidirect relators in the left-right action
target: relative-kazhdan-bimodule-requires-whole-module-covariance
requires: []
---

The two maps `lambda_s` and `mu` are homomorphisms on `M` and on `A`
separately, so their left-right product is a unitary representation of the
free product.  The defining mixed relator of `Gamma` is

```text
r(a,m)=a m a^(-1) (a m)^(-1).
```

The right representation kills this relator exactly precisely when

```text
pi(a)rho(m)pi(a)^*=rho(a m).                            (RKB1)
```

The left representation gives the same condition after conjugating the
indices by `s`.  Thus both factors are representations of `Gamma`, and
hence give the canonical left-right bimodule, exactly when `(RKB1)` holds
for every `a,m`.

Quantitatively, the defect of `mu` on `r(a,m)` is exactly

```text
||pi(a)rho(m)pi(a)^*-rho(a m)||_2.                      (RKB2)
```

and `lambda_s` has the corresponding conjugated defect.  Taking a supremum
over the mixed relators therefore gives the whole-module covariance
quantity, not a finite-presentation defect.

There is one harmless logical weakening to record.  A left-right
superoperator `X |-> LXR^*` can be the identity even when neither `L` nor
`R` is the identity, but then `L=R=lambda I` for a scalar `lambda`.  Hence
descent of `Theta_s` without descent of its two factors still requires the
two covariance-error unitaries to match projectively for every moving
`m`.  This is the projective whole-module gate, not finite seed covariance.

A relative Kazhdan projection belongs to `C^*(Gamma)` and can be evaluated
with its spectral-gap estimate only in an actual representation of
`Gamma`; ordinary property `(T)` gives no contractive functional calculus
for the merely approximate free-product action above.  This proves the
claim.
