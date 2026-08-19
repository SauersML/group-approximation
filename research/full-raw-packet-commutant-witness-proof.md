---
rg: 2
id: full-raw-packet-commutant-witness-proof
kind: route
title: Project onto the raw packet algebra and Haar-average its commutant
target: full-raw-packet-commutant-witness
requires: []
artifacts:
  - notes/TRUE_FULL_RAW_PACKET_COMMUTANT_WITNESS.md
  - experiments/atlas-pauli-transported-carrier.json
---

The exact certificate gives `|K|=16` and
`K intersect U^*KU={1}`.  Finite Fourier projection therefore sends the
transported carrier to `(1/4)1`, leaving squared normalized-HS residual
`1/4-(1/4)^2=3/16`.  Fixed finite Gram-matrix inversion carries the identity
to trace-preserving matrix coordinates.  The standard commutant Haar identity

```text
integral ||[V,X]||_2^2 dV = 2||X-E_A(X)||_2^2
```

then produces one witness with asymptotic squared energy at least `3/8`.
