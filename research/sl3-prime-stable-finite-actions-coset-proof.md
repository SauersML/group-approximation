---
rg: 2
id: sl3-prime-stable-finite-actions-coset-proof
kind: route
title: Specialize the stable-finite-actions coset obstruction to the arithmetic pair
target: sl3-prime-stable-finite-actions-excludes-coset-soficity
requires:
  - stable-finite-actions-blocks-codense-kazhdan-coset-soficity
  - sl3-prime-permutation-codensity
---

The actor `Gamma` is linear over a characteristic-zero field and residually
finite.  The stabilizer `Lambda=SL_3(Z)` has property `(T)`, hence a fixed
finite Kazhdan set and constant.  Prime-uniform permutation co-density gives
`rho(Lambda)=rho(Gamma)` in every finite action.  These are precisely the
three hypotheses of the generic theorem, proving the conditional
nonsoficity statement.
