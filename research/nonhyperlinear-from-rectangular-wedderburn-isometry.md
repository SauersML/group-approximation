---
rg: 2
id: nonhyperlinear-from-rectangular-wedderburn-isometry
kind: route
title: A rectangular coefficient isometry contradicts every finite regular atlas microstate
target: non-hyperlinear-group
requires:
  - leavitt-regular-atlas-hyperlinearity-criterion
  - rectangular-wedderburn-block-isometry-gap
  - atlas-rectangular-wedderburn-isometry-certificate
---

Assume the prerequisites and suppose the binary Leavitt unit group were
hyperlinear.  The regular-atlas criterion gives multiplicities `k_n`, relative
chart unitaries `U_n`, and packet defects `delta_n -> 0`.

Choose the fixed irreducibles and coefficient expression from
`atlas-rectangular-wedderburn-isometry-certificate`.  Then

```text
||p_tau-X(U_n)^*X(U_n)||_2 <= C delta_n^c -> 0.       (NRW1)
```

But `d_sigma<d_tau`, so
`rectangular-wedderburn-block-isometry-gap` gives for every `n`

```text
||p_tau-X(U_n)^*X(U_n)||_(2,ambient)^2
 >= (d_tau-d_sigma)/|A_8| > 0.                       (NRW2)
```

The fixed positive lower bound contradicts `(NRW1)`.  Therefore no such
regular-atlas microstate sequence exists, and the explicit binary Leavitt unit
group is nonhyperlinear.

This route leaves exactly one new atlas-specific theorem: discover one
rectangular Fourier block whose Gram defect is forced by the finite packet.
The finite coefficient compiler and ideal-certificate lemma turn that theorem
into a bounded symbolic proof-search problem rather than an unbounded
multiplicity reconstruction.