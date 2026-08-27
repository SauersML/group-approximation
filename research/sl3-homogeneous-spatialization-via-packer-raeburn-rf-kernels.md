---
rg: 2
id: sl3-homogeneous-spatialization-via-packer-raeburn-rf-kernels
kind: route
title: Stabilize the return cocycle and descend through residual finite-index kernels
target: sl3-homogeneous-quotient-crossed-product-is-connes-embeddable
requires:
  - sl3-homogeneous-ce-is-common-cocycle-spatialization
  - finite-quotient-fell-untwisting-leaves-kernel-cocycle
---

Use the infinite Packer--Raeburn regular gauge to untwist the lattice-return
cocycle, then approximate the regular lattice orbit by finite residual
quotients.  The hoped-for endpoint is a normalized finite model in which the
return implementers are coherent over one embedding of the profinite corner.

The unresolved step is the holonomy of the stabilizer kernel of each finite
orbit.

The literal infinite-stabilization compression branch is now closed by
`regular-stabilization-finite-corners-have-spectral-leakage`: nonamenability
forces a uniform return leak from every finite-rank corner, even when the
corner mixes all regular orbit labels.  Passing to finite quotient regular
representations removes that spectral gap only by producing the section
kernel cocycle in `finite-quotient-fell-untwisting-leaves-kernel-cocycle`.
Thus this route has no intermediate “almost finite regular gauge”: it must
solve the full residual-kernel spatialization problem.
