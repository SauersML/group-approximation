---
rg: 2
id: center-chain-hecke-arms-have-native-masses
kind: claim
title: Two center-chain Hecke arm compressions have the native quarter and eighth masses
artifacts:
  - research/center-chain-hecke-mass-proof.md
distinct_from:
  center-chain-character-atom-gives-scalar-gram: that obtains maximal Gram for the two disjoint literal selector roots but loses the Pauli arms; this compresses the moving arms themselves and obtains the two native dyadic masses from their subgroup intersections.
  hecke-quarter-selector-is-untyped-or-rank-preserving: that rules out treating a quasi-regular fixed-coset fraction as a universally authenticated selector rank; this computes canonical regular-trace Hilbert--Schmidt masses of two named character-corner operators and makes no claim that their polar supports already have those ranks.
  binary-leavitt-native-two-scale-cross-gram-positive: that requires controlled-selector normal forms, a common positive polar corner, and mixed-Pauli estimates; this supplies only the exact two scalar masses which a successful polar authentication would have to consume.
---

Retain the finite center-chain subgroup `H~=UT_4(F_2)`, its character atom
`e=e_chi`, and the chained arms

```text
A_1=x_47(a_1),              A_2=x_58(a_2),
a_m=s_1t_(0^m)
```

from `center-chain-character-atom-gives-scalar-gram`.  Then the two literal
Hecke compressions

```text
T_1=eA_1e,                  T_2=eA_2A_1e               (CHA1)
```

have exact canonical normalized-Hilbert--Schmidt masses

```text
||T_1||_2^2=(1/4)tau(e)=1/256,
||T_2||_2^2=(1/8)tau(e)=1/512.                         (CHA2)
```

Indeed, conjugation by `A_1` fixes exactly the index-four subgroup of `H`
whose `(6,4)` and `(5,4)` matrix coordinates vanish.  Conjugation by
`A_2A_1` fixes exactly the index-eight subgroup on which, in addition, the
`(6,5)` coordinate vanishes.  On both intersections the transported
character equals `chi`, so the finite-character Hecke formula gives `(CHA2)`.

The numbers in `(CHA2)` are exactly the dyadic label fractions required by
the two native selector rows.  They are not, by themselves, an
authentication: a general Hecke compression need not be a scalar multiple
of a partial isometry, and its support trace is not determined by its
Hilbert--Schmidt mass.  For these two named operators, however,
`center-chain-hecke-polar-supports-are-nested-pauli-flags` now solves that
spectral question completely.  Their squared absolute values are nested
support projections of relative traces `1/4` and `1/8`; the smaller support
reduces the source Pauli pair, and the relative polar gauge has both mixed
Pauli commutators equal to zero.  The remaining question is only whether
these exact Hecke flags are the prescribed stabilized occurrences of the
two native selector rows.

DERIVATION
center-chain-hecke-mass-proof
