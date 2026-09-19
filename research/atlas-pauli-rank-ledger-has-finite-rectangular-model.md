---
rg: 2
id: atlas-pauli-rank-ledger-has-finite-rectangular-model
kind: claim
title: The Atlas Pauli rank ledger has an exact finite rectangular model
distinct_from:
  atlas-fixed-packet-arithmetic-has-no-hs-gap: that proves the general projective-semigroup density theorem; this computes the actual Atlas denominators and gives a concrete finite Pauli model realizing both module degrees.
  first-leavitt-weyl-cell-has-exact-rectangular-model: that constructs the general characteristic-p rectangular packet; this specializes it to the binary Atlas carrier dimensions and rules out the proposed bare rank-integrality extraction.
  four-pauli-cross-gram-exact-completeness-firewall: that obstructs four simultaneous intertwiners on positive overlap; this proves that none of the required obstruction comes from the separate packet ranks or their fixed rational carrier weights.
---

**ESTABLISHED FIREWALL.**  In the exact regular-Atlas normalization the
ambient matrix dimension is

```text
d=20160 k=64*315 k.                                    (PRL1)
```

Consequently every fixed packet weight with denominator dividing `64` is
integral in every allowed dimension.  In particular the half and quarter
carriers have ranks

```text
d/2=10080 k,                 d/4=5040 k,               (PRL2)
```

and even a hypothetical projection of trace `5/64` would have the integral
rank `1575 k`.  The actual cross-Gram quantity `5/64` is a squared
Hilbert--Schmidt mass, not a projection rank; `(PRL1)` only records that its
denominator cannot create an integrality obstruction.

On a quarter carrier of dimension `5040 k`, both relevant semisimple module
degrees fit exactly:

```text
M_2 source multiplicity =2520 k,
M_4 target multiplicity =1260 k.                       (PRL3)
```

This compatibility is realized, rather than merely counted.  On
`K=C^2 tensor C^2`, use the exact rectangular Pauli model

```text
X_src=X tensor 1,       Z_src=Z tensor 1,
D_1=X tensor 1,         D_2=Z tensor 1,
D_3=1 tensor X,         D_4=1 tensor Z,                (PRL4)
```

with the identity and swap as the two branch transports.  The source algebra
is `M_2 tensor 1_2`, the target words generate `M_4`, and all source,
two-child, branch, return, commutator, and Pauli trace tables hold exactly.
Taking `5040 k` direct-sum copies puts this model in the canonical Atlas
dimension `(PRL1)` without changing any normalized trace or HS statistic.

Therefore no argument using only

1. ranks of the named half/quarter packet carriers;
2. divisibility or congruence of their multiplicities;
3. the separate source and target finite Pauli types; or
4. the local branch and return tables

can extract the common four-intertwiner carrier required by
`atlas-kernel-relators-couple-cross-gram-to-four-pauli`.  These data already
have exact finite models at every allowed Atlas amplification.

This does **not** construct a countermodel to the full mixed Atlas kernel and
does not realize the compulsory cross-Gram as a four-word intertwiner.  On
the contrary, `four-pauli-cross-gram-exact-completeness-firewall` proves that
positive overlap cannot intertwine `(PRL4)` in all four directions.  The
remaining finite-matrix-only target must consequently use mixed full-kernel
relations to select a singular subspace, a relative position of multiplicity
spaces, or another coordinate invariant not determined by this rank ledger.
