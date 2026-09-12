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

## Why the abstract route was never going to be enough

`local-exactification-invariants-cannot-close-gluing-holes` identifies
`Alg(rho_n(K))'` as this lane's residual gauge group: exactifying the packet
determines the microstate only up to conjugation by that commutant, and the
witness of `full-raw-packet-commutant-witness` is produced by Haar averaging
over exactly that group, with `||[V_n,F_n]||_2^2>=3/8-o(1)`.  Any observable
built inside `Alg(rho_n(K))` is therefore constant along the very direction
that has to be detected, which is the structural reason a bicommutant theorem
about one packet cannot substitute for the cross-root relations already
required above.  The reformulation this suggests is to classify which
commutant modes survive the cross-root transition relations, rather than to
quantify `||[V,F]||_2` over all `V` in the commutant at once.
