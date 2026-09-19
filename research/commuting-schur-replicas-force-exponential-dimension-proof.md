---
rg: 2
id: commuting-schur-replicas-force-exponential-dimension-proof
kind: route
title: Select one bad context per replica and count violations on a joint spectral sector
target: commuting-schur-replicas-force-exponential-dimension
requires:
  - non-ce-bcs-has-finite-dimensional-forbidden-mass-gap
  - schur-packet-flips-realize-predicate-cocycle
  - projective-holonomy-rank-forces-exponential-multiplicity
---

Normalize trace on the nonzero `J=-1` carrier.  In replica `i`, `(FMG)` says
that the sum of the `C` context-forbidden masses is at least `beta_B`; choose
`c_i` with mass at least `b=beta_B/C`, and let `Q_i` be the sum of its
forbidden joint selector projections.  Cross-replica commutation makes the
`Q_i` commuting projections.  If `K=sum_i Q_i`, then

```text
tau(K)>=bN.
```

In their joint spectral decomposition, `K` has integer eigenvalues.  Hence a
nonzero joint sector has eigenvalue `k>=ceil(bN)`.  Refine it by the selector
characters of the chosen contexts.  At each of the `k` forbidden sites,
`schur-packet-flips-realize-predicate-cocycle` supplies one symplectic block in
the packet implementer cocycle.  The site algebras commute, so these blocks
are independent and the total cocycle rank is `2k`.

Factor the irreducible packet modules on this refined invariant sector.
`projective-holonomy-rank-forces-exponential-multiplicity` gives `2^k` as a
divisor of the remaining multiplicity.  The sector is nonzero, so its Hilbert
dimension is at least `2^k>=2^(ceil(bN))`; the full marked carrier is at least
as large.

