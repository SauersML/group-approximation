---
rg: 2
id: sl3-residual-kernel-spatialization-is-goal-equivalent
kind: claim
title: Spatializing any finite-index return kernel is equivalent to spatializing the whole lattice
artifacts:
  - research/sl3-residual-kernel-spatialization-equivalence-proof.md
invalidates:
  - sl3-homogeneous-spatialization-via-packer-raeburn-rf-kernels
distinct_from:
  finite-quotient-fell-untwisting-leaves-kernel-cocycle: that shows a finite quotient retains a kernel cocycle; this proves that, for the homogeneous quotient, solving the retained finite-index kernel is already equivalent to solving the full return cocycle.
---

**ESTABLISHED PROPERTY-(T)-FREE FIREWALL.**  Let

```text
P_Gamma = B rtimes_(beta,c) Gamma
```

be the finite cocycle crossed product in `(HCS3)`, where
`Gamma=Lambda'`.  For every finite-index subgroup `H<=Gamma`, put

```text
P_H = B rtimes_(beta,c|H) H.                            (RKS1)
```

Then `P_H subset P_Gamma` has Jones index `[Gamma:H]`, and

```text
P_H is CE  iff  P_Gamma is CE.                         (RKS2)
```

Equivalently, common `R^omega` spatialization of the return cocycle
restricted to `H` exists if and only if common spatialization of the full
`Lambda'` cocycle exists.  Thus residual finite quotients do not provide an
intermediate spatialization theorem: their stabilizer-kernel problem is the
original homogeneous-quotient problem at finite index.

DERIVATION
sl3-residual-kernel-spatialization-equivalence-proof
