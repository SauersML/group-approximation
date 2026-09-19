---
rg: 2
id: affine-weyl-apartment-independent-lamp-models-proof
kind: route
title: Reduce the apartment modulo expanding translation sublattices and use finite regular representations
target: affine-weyl-apartment-has-independent-lamp-models
requires: []
---

For `T = Z^2` and the finite signed Weyl group `K`, reduce
`T rtimes K` modulo `mT` and form the finite permutation wreath product

```text
G_m = C_2^(T/mT) rtimes ((T/mT) rtimes K).
```

Every fixed nonidentity word in
`C_2^(T) rtimes (T rtimes K)` survives for all sufficiently large `m`, so
the left regular representations of the `G_m` have the canonical trace in
the limit.  The origin lamp and its translate by `h` are distinct commuting
involutions.  Expanding their two spectral projections against the regular
character gives traces `1/2,1/2` and intersection trace `1/4` exactly.

All translation, Weyl, stabilizer, covariance, and apartment-lamp
commutation relations hold exactly in every `G_m`.  These finite regular
models therefore prove the claim and show that an interior-overlap exclusion
must use nonmonomial root-group relations gluing different apartments.
