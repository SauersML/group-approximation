---
rg: 2
id: jacobson-corona-centralizer-does-not-lift-to-base-commutants
kind: claim
title: An exact coherent base has a corona-centralizing shift at distance one from every coordinate base commutant
distinct_from:
  corona-commutant-growth-witness: that uses slow phases to separate two infinite subgroup commutants; this authenticates the full coherent base and finite intertwining while separating its entire coordinate commutant from a corona-centralizing shift.
  jacobson-full-packet-spectral-cuts-do-not-preserve-norm: that obstructs spectral cuts without modeling the full base; this is an actual asymptotic representation factoring through the faithful arithmetic quotient, with the entire base exact.
artifacts:
  - research/artifacts/jacobson-corona-centralizer-does-not-lift-to-base-commutants-2026-09-08.md
---

There are exact base representations `rho_n:EL_3(J)->U(d_n)` and
unitaries `T_n` commuting with the full constant `GL_3(F_2)` such that

```text
||[T_n,rho_n(a)]|| -> 0       for every fixed base element a,
dist_op(T_n,rho_n(EL_3(J))')=1       for every n.
```

The resulting norm-corona representation is faithful on
`SL_3(F_2[z,z^(-1)]) x Z`. Its pullback to `Gamma_triangle`
kills precisely the finitary subgroup `L`. All finite tables and
finite intertwining tests are exact; only the stable-h word has a
nonzero defect, tending to zero.

Fixed rounds of finite-packet conditional expectations leave these
unitaries far from the full base commutant. This disproves correction
into that commutant with the entire base fixed and without a retained
head hypothesis. It neither treats joint correction nor decides the
marked gap.

DERIVATION
jacobson-finite-field-coset-phase-proof
