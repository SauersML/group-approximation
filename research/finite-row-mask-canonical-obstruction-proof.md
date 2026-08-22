---
rg: 2
id: finite-row-mask-canonical-obstruction-proof
kind: route
title: Evaluate the finite group-algebra packet in a canonical matrix ultraproduct
target: finite-row-mask-group-algebra-certificate-forces-nonhyperlinear
requires:
  - independent-row-masks-transfer-bcs-gap-to-ambient-identity
  - finite-matrix-defect-zero-is-exact-ultraproduct-realizability
---

If `Gamma` were hyperlinear, evaluate every finite group-algebra expression
in a canonical tracial matrix-ultraproduct embedding.  The PVM, involution,
projection, and annihilation identities are exact there.  Choose bounded
matrix representatives and use the dimension-free stability of each fixed
finite PVM/projection/involution relation to obtain exact matrix PVMs,
projections, and involutions with `o(1)` change.  The annihilation rows remain
`o(1)` by bounded multiplication, while canonical trace preservation gives

```text
tr(1-q_j^(n))->tau_Gamma(1-q_j).                       (RMC4)
```

Apply `independent-row-masks-transfer-bcs-gap-to-ambient-identity` and pass
to the limit.  It yields `Delta<=D_row`, contradicting `(RMC3)`.

All expressions and identities have finite support.  Compile them into one
finite unitary polynomial-and-trace packet.  If its all-dimensional defect
infimum were zero, `finite-matrix-defect-zero-is-exact-ultraproduct-realizability`
would produce the forbidden exact ultraproduct tuple.  Hence its infimum is
a positive `epsilon_0`.  Normalized trace and normalized Hilbert--Schmidt norm
are unchanged by tensoring every matrix with an identity.

