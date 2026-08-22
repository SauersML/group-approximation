---
rg: 2
id: relative-kazhdan-bimodule-requires-whole-module-covariance
kind: claim
title: The canonical relative-Kazhdan factor bimodule requires whole-module covariance
artifacts:
  - research/artifacts/whole-module-kazhdan-mixed-word-audit-2026-08-21.md
distinct_from:
  property-t-must-upgrade-global-augmentation-rounding: that asks for a positive matrix-rounding theorem; this computes why the obvious relative-property-T bimodule cannot be formed before that theorem.
  finite-covariance-energy-sees-only-character-restrictions: that computes the kernel of finite diagonal covariance tests; this is the separate exactness obstruction to applying a Kazhdan projection to the proposed left-right Hilbert--Schmidt action.
---

Let `Gamma=M rtimes A`, let `rho:M->U(d)` and `pi:A->U(d)` be exact
representations of the two factors separately, and fix `s in A`.  On the
Hilbert--Schmidt space define left and right actions of the free product
`M*A` by

```text
lambda_s(m)=rho(s m),       lambda_s(a)=pi(s a s^(-1)),
mu(m)=rho(m),               mu(a)=pi(a),
Theta_s(g)X=lambda_s(g) X mu(g)^*.
```

Then `Theta_s` is an exact unitary representation of `M*A`.  Both factor
actions descend to honest representations of the semidirect product
`Gamma` if and only if the original pair `(rho,pi)` has exact covariance

```text
pi(a)rho(m)pi(a)^*=rho(a m)       for every a in A, m in M.
```

Consequently relative property `(T)` of `(Gamma,M)` cannot by itself upgrade
finite seed covariance to whole-module covariance through this bimodule.
The standard relative Kazhdan bimodule is therefore available only after
the desired global covariance has made both factors representations.
Allowing cancellation between the two factors weakens exact descent only to
**projective** whole-module covariance: the two mixed-relator errors must
agree as scalars.  That is still a moving all-module condition, not a
consequence of the finite seed tests.

This does not rule out a lamp-coupled stability theorem which first corrects
the factors, or proves projective covariance by another mechanism.  It
rules out the direct argument
"form the bimodule and apply relative `(T)`" without such a correction.
