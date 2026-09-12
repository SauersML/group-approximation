---
rg: 2
id: commuting-lamp-mf-radical-self-cover-route
kind: route
title: Canonical compressor self-cover computes the level-even radical
target: commuting-lamp-mf-radical-is-level-even
requires:
  - commuting-lamp-quotient-structure
  - commuting-lamp-quotient-not-mf
  - coset-compression-renormalization
  - doubling-quotient-residually-finite
artifacts:
  - research/artifacts/radical-renormalization-2026-08-23.md
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

For the affine pair take `s=tau`.  The canonical coset self-cover from
`coset-compression-renormalization` becomes in the established coordinates

```text
r(n,y)=(n-1,2y),       X=Z x (Z[1/2]/Z)^3.
```

Its `m`-th iterate is `(n,y)|->(n-m,2^m y)`.  Since every dyadic-torus element
has finite 2-power order, two sites are eventually merged iff they have the
same level.  Hence the stable lamp-pushforward kernel is exactly `L_0`, the
subgroup of configurations of even parity on every level.  Radical
automorphization gives `L_0 <= Rad_MF`.

The terminal quotient is
`(directSum_Z C_2) semidirect V`, which `doubling-quotient-residually-finite`
proves residually finite and hence MF.  The exact-quotient clause therefore
gives `Rad_MF=L_0`.
