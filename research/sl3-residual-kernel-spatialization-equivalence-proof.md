---
rg: 2
id: sl3-residual-kernel-spatialization-equivalence-proof
kind: route
title: Identify finite-orbit stabilizer holonomy with a finite-index cocycle crossed product
target: sl3-residual-kernel-spatialization-is-goal-equivalent
requires:
  - sl3-homogeneous-ce-is-common-cocycle-spatialization
  - finite-index-extensions-preserve-connes-embeddability
  - finite-quotient-fell-untwisting-leaves-kernel-cocycle
---

The Fourier decomposition over right cosets `H\Gamma` writes
`L^2(P_Gamma)` as the direct sum of `[Gamma:H]` right `P_H`-modules.  The
canonical expectation onto the `H`-Fourier coefficients therefore makes
`P_H subset P_Gamma` a finite-index inclusion with Jones index
`[Gamma:H]`.  Finite-index invariance of Connes embeddability gives `(RKS2)`.

Apply `sl3-homogeneous-ce-is-common-cocycle-spatialization` first to
`Gamma`, and then to the restricted cocycle action of `H`.  It identifies CE
of the two crossed products with the corresponding common-ultrapower
spatialization problems, proving their equivalence.

The infinite regular Packer--Raeburn gauge lives over
`B tensor B(ell^2 Gamma)` and has no finite tracial unit.  Compressing to a
finite orbit `Gamma/H` restores a normalized trace, but its basepoint
compression is precisely the `H`-cocycle model above.  Hence the residual
finite-index step cannot remove the open holonomy.
