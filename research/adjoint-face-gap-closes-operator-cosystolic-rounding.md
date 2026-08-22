---
rg: 2
id: adjoint-face-gap-closes-operator-cosystolic-rounding
kind: route
title: Feed the repeated-LDPC adjoint gap into parity-aware pinching and classical decoding
target: operator-unique-neighbor-cosystolic-rounding
requires:
  - repeated-ldpc-shared-face-marginal-synchronization
  - repeated-ldpc-adjoint-face-hamiltonian-gap
  - gapped-face-pinchings-give-same-hilbert-code-pvm-rounding
---

Synchronize repeated face PVMs with literal shared marginals, apply the gapped face-Hamiltonian theorem
separately to X and Z, and use the classical LTC correction on the resulting
central joint PVMs.  This gives the same-Hilbert code actions and uniform
modulus required by the operator-cosystolic target.  The mixed Weyl sampler
and private basins remain downstream; unbounded word-placement holonomy is a
separate syntactic gate.
