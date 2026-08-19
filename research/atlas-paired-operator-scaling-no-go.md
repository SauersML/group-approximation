---
rg: 2
id: atlas-paired-operator-scaling-no-go
kind: claim
title: Fixed two-term finite-chart equations cannot yield the atlas shrunk-space certificate
artifacts:
  - docs/TRUE_ATLAS_SINGLE_BRIDGE_SUBGROUP_REDUCTION.md
distinct_from:
  pure-finite-group-operator-scaling-collapses-to-multiplicity: that theorem handles ordinary same-group intertwining and vanishing cutoffs; this no-go allows arbitrary fixed pairs of elements from the two A8 charts and rules out shrinkage at every cutoff when the paired equations are exact in the canonical regular-trace atlas model.
  atlas-spectral-shrunk-intertwiner-certificate: that open target remains viable because its quadratic form may use genuinely mixed or multi-term atlas information; this theorem only removes the tempting fixed paired-equation implementation.
---

After exactifying the two regular-`A_8` chart packets, consider any quadratic
form built from a fixed finite list of **two-term paired equations**

```text
E(T)=sum_s ||rho_1(a_s)T-T rho_2(b_s)||_2^2,
a_s,b_s in A_8,                                         (APN1)
```

where every displayed equation is exact for the relative chart implementer in
the canonical tracial atlas model.  Then no spectral low-energy space of `E`
on common finite regular-chart amplifications has a nonzero shrunk-subspace
deficiency.

Equivalently, an implementation of
`atlas-spectral-shrunk-intertwiner-certificate` cannot obtain `(ASI3)` from a
fixed sum of paired chart-intertwining defects of the form `(APN1)`, regardless
of the spectral threshold.

## Consequence for the operator-scaling lane

The low-energy matrix space must receive information which is absent from a
single finite subgroup of `A_8 x A_8`.  At least one of the following has to
occur:

- a genuinely multi-term linear constraint, not reducible to `A T = T B`;
- coefficients or selected singular directions depending on the finite
  microstate/multiplicity data; or
- a nonlinear operation before the matrix-space certificate is formed.

This explains why boundary alignment and single-bridge relations alone do not
produce noncommutative-rank pressure: if they are packaged only as exact
paired conjugacy equations, regular-trace compatibility forces their product
subgroup to be balanced and the zero-energy matrix space already contains a
unitary.
