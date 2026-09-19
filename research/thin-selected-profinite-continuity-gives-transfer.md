---
rg: 2
id: thin-selected-profinite-continuity-gives-transfer
kind: route
title: Selected profinite continuity and the thin tau gap imply robust relative-commutant transfer
target: thin-sln-robust-relative-commutant-transfer
requires:
  - thin-selected-module-is-profinite-continuous
  - thin-profinite-selected-gap-lemma
  - sln-z-thin-codense-tau-pair
---

If the finite-stage modulus `(TRC1)` failed, choose defects tending to zero
while the commutator with the fixed outsider stays bounded below.  Passing
to a tracial matrix ultraproduct gives an exact representation

```text
pi:A->U(M_omega)
```

and a unitary `v` which centralizes `C` but not the outsider.  By
`thin-selected-module-is-profinite-continuous`, its selected cyclic module
`K_v` is weakly contained in `pi_FD^0`.  The gap in
`thin-profinite-selected-gap-lemma`, supplied for the explicit thin pair by
`sln-z-thin-codense-tau-pair`, then forces `(1-P_A)v=0`.  Hence `v`
centralizes all of `A`, contradicting the surviving outsider commutator.

This proves the qualitative ultraproduct statement `(TRC2)`.  The usual
compactness contradiction gives the dimension-free modulus `(TRC1)`.
