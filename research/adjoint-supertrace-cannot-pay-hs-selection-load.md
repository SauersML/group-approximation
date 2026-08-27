---
rg: 2
id: adjoint-supertrace-cannot-pay-hs-selection-load
kind: claim
title: A small adjoint subspace can carry a macroscopic matrix spectral cut
distinct_from:
  predicate-rank-jump-forces-adjoint-reynolds-gap: that proves the entire packet Reynolds-difference range has positive normalized adjoint rank when forbidden Hilbert mass is positive; this shows one or finitely many selected adjoint directions need not have comparable carrier mass.
  marked-hs-separation-forces-spectral-density: that extracts a positive matrix-corner carrier directly from the normalized HS norm of one unitary word; this refutes extracting such a carrier from the normalized supertrace dimension of an operator-space subspace.
---

There is no universal constant `C` such that, for every `d`, every subspace
`E<=M_d(C)`, and every self-adjoint `x in E`, the matrix trace of the support
or a balanced spectral cut of `x` is bounded by

```text
C rank(P_E)/d^2,
```

where `P_E` is the orthogonal projection onto `E` in the `d^2`-dimensional
adjoint Hilbert space.  The failure already occurs for `dim E=1`: a balanced
sign matrix has positive spectral projection of trace `1/2`, and the identity
has support trace one, while the normalized adjoint rank of their spans is
`1/d^2`.

Consequently an adjoint spectral or supertrace argument cannot pay a
positive-density HS carrier merely by selecting one low-energy direction.
The escape used by the Schur--Clifford route is quantitative density of the
**whole** Reynolds-difference range, not support of one chosen vector.
