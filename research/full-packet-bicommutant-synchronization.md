---
rg: 2
id: full-packet-bicommutant-synchronization
kind: claim
title: Synchronize every raw-packet commutant symmetry with the transported carrier
distinct_from:
  pauli-carrier-membership-decoder: This asks for commutation with every unitary in the full raw-packet commutant; the other asks directly for membership in the smaller binary algebra of one parent projection.
  outer-pvm-synchronization: This is a finite-multiplicity bicommutant statement; the other synchronizes two outer transition measurements into one PVM.
---

For every trace-preserving finite matrix microstate of the fixed atlas
presentation, after exactifying the raw finite packet `K`, prove uniformly
for coordinate unitaries `V_n in Alg(rho_n(K))'` that

```text
||[V_n,F_n]||_2 -> 0,
```

where `F_n` is the comb-transported Pauli carrier.  The proof must use the
cross-root multiplication and compressor synchronization relations; the
regular representation shows that no abstract finite-von-Neumann-algebra
bicommutant theorem can suffice.
