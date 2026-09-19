---
rg: 2
id: kt-honest-actor-tensor-seam-cancellation-proof
kind: route
title: Cancel the quotient actor in the tensor-product cocycle
target: kt-honest-actor-tensor-extensions-do-not-change-the-seam
requires:
  - kt-c-normalization-seam-is-a-relative-commutant-cocycle
  - kt-passive-mcduff-amplification-does-not-close-the-seam
---

Using `(KAT1)`, the conjugated and named Gamma implementations are

```text
v'_gamma
 =v_gamma tensor (sigma_C sigma_gamma sigma_C^*),
rho'_gamma
 =rho_gamma tensor sigma_(alpha_C(gamma)).
```

The two second tensor factors are equal because `sigma` is a representation
of the quotient `G`, where `C gamma C^(-1)=alpha_C(gamma)`.  Therefore

```text
v'_gamma(rho'_gamma)^*
 =(v_gamma rho_gamma^*) tensor 1,
```

which is `(KAT2)`.  The remaining statements are exactly the distinction
between an honest tensor actor (where this cancellation applies) and a
partial block table (which has not satisfied the `SL_3(Z)` relators).
