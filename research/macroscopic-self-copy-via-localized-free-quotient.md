---
rg: 2
id: macroscopic-self-copy-via-localized-free-quotient
kind: route
title: Turn a predicate packet inclusion into a child-only adjoint sector through a free self-compressor
target: marked-self-copy-forces-macroscopic-adjoint-excess
requires:
  - finite-inclusion-is-free-self-compressor-quotient
  - shared-bcs-carrier-localizes-free-compressor-quotient
  - predicate-rank-jump-forces-adjoint-reynolds-gap
---

Use the free self-compressor with parent quotient `B_f` and child quotient
`A_f`.  Carrier-localized quotient factorization identifies the packet
Reynolds difference with a subspace fixed by the child action and moved by a
parent generator.  The predicate rank-jump theorem bounds its normalized
adjoint rank below by a fixed quadratic function of forbidden mass.  Robust
finite-matrix BCS soundness makes that mass positive whenever the marked
carrier survives, giving exactly the projection required by
`marked-self-copy-forces-macroscopic-adjoint-excess`.

In the exact infinite tracial model the forbidden mass is zero, so the
localized Reynolds difference vanishes and the HNN relations remain
consistent.  Thus the strict finite-matrix conclusion is not asserted in
the regular or perfect infinite representation.

