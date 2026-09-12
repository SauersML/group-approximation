---
rg: 2
id: split-higman-cycle-proof
kind: route
title: Put the exact periodic clock pair on every split doubling edge
target: split-higman-cycle-has-haar-marginals-and-maximal-role-gap
requires:
  - periodic-bs-clock-defeats-spectral-first-hit-checksum
---

Replace each cyclic generator `g_i` by two occurrence symbols: `c_i` in its
role as conjugator of `g_(i+1)`, and `z_i` in its role as the target of
`g_(i-1)`.  The split edge equations are

```text
c_i z_(i+1) c_i^(-1)=z_(i+1)^2.
```

On one fixed `q`-dimensional space set every `c_i=P_q` and every `z_i=Z_q`.
The periodic Baumslag--Solitar clock identity makes all four equations exact.
The marginal moment and Hilbert--Schmidt calculations are `(PBC2)--(PBC3)`.

Gluing the split presentation imposes `c_i=z_i`.  The model violates each of
these identifications by squared normalized Hilbert--Schmidt distance
`2-2/q`, despite matching every fixed marginal power moment asymptotically.
This proves both the countermodel and its exact limitation.

