---
rg: 2
id: lin-state-dependent-gh-preserves-the-commutant
kind: claim
title: State-dependent finite-group exactification preserves the complete opposite algebra
artifacts:
  - research/artifacts/lin-tracial-rounding-state-gh-source-audit-2026-08-23.md
distinct_from:
  gowers-hatami-finite-group-hs-stability: that is a normalized-Hilbert--Schmidt finite-matrix theorem with dimension control; this is a density-seminorm theorem in a finite von Neumann algebra whose dilation intertwines the full commutant.
---

Let `G` be finite, let `A` be a finite tracial von Neumann algebra in
standard form, and let `phi:G->U(A)` be an average `(epsilon,rho)`
representation for a positive density `rho`.  There are an isometry
`V:H->H tensor C^{|G|}` and an exact representation
`phi':G->U(A tensor B(C^{|G|}))` such that

```text
V B=(B tensor I)V                         for every B in A',
E_g ||phi(g)-V^*phi'(g)V||_rho^2 <= epsilon.
```

Thus exactifying one finite left/Pauli packet does not disturb the right or
opposite algebra through the dilation.  This does **not** lock a common
right/payload carrier: the exact representation lives on a flexible
amplification, its compression need not be a representation, the estimate
sees only the chosen density, and neither the isometry nor that density's
support is word-visible.  Different densities may retain unrelated carrier
and multiplicity gauges.
