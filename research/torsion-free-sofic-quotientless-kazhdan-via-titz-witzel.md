---
rg: 2
id: torsion-free-sofic-quotientless-kazhdan-via-titz-witzel
kind: route
title: A sofic Titz--Witzel simple lattice is a torsion-free sofic quotientless Kazhdan group
target: torsion-free-sofic-quotientless-kazhdan-group-exists
requires:
  - titz-witzel-kernel-sofic
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
---

Let `K` be the smallest Titz Mite--Witzel lattice of `titz-witzel-kernel-sofic`. By
`titz-witzel-simple-kazhdan-cat0-lattices-exist` (Corollary B of arXiv:2509.05054v2, recorded
there), `K` is infinite, simple, torsion-free, and has property (T). An infinite simple group has
no nontrivial finite quotient: the kernel of a map to a finite group is normal, so it is `1` or
`K`, and it cannot be `1`. Assuming `titz-witzel-kernel-sofic`, `K` is sofic. So `K` witnesses
`torsion-free-sofic-quotientless-kazhdan-group-exists`.

This is a one-step conditional implication. It is recorded so that the gate has a route. The
Titz--Witzel route to the goal needs more: that the kernel is not MF (`titz-witzel-residual-is-mf`).
The gate does not need that.
