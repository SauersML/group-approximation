---
rg: 2
id: kazhdan-asymptotic-commutant-transport-proof
kind: route
title: Finite-ultraproduct proof of Kazhdan commutant transport
target: kazhdan-asymptotic-commutant-transport
requires: []
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/ManuscriptKazhdanTransport.lean
---

## Direct proof

The adjoint coordinate maps define an honest unitary representation on the
Hilbert ultraproduct and an integrated representation in the finite norm
ultraproduct of the coordinate operator algebras.  The Kazhdan projection
cuts out the fixed subspace.  One-sided compression includes this projection
in its unitary conjugate; finiteness and Murray--von Neumann equivalence force
equality.  The equality transports every fixed vector, which is precisely the
asserted normalized Hilbert--Schmidt commutator convergence.  The manuscript
gives the subsequence argument upgrading ultrafilter convergence to ordinary
convergence, and the cited closed Lean theorem checks the complete statement.

## What discharges `requires: []`

The closed theorem behind this route is
`KazhdanAsymptoticCommutant.finiteStageKazhdanTransport`, the **quantitative
finite-stage** proof of Appendix `app:finite-stage` announced by Remark
`rem:finite-stage`: it runs at each single coordinate, with an explicit
almost-fixed spectral subspace of the averaged adjoint action in place of the
Kazhdan projection and the equal-rank reversal estimate in place of finiteness
of the norm ultraproduct.  It has no unconstructed input, which is why this
route commits to `requires: []`, and it gives error bookkeeping in `kappa`,
`|S|`, the uniform bound on `(x_n)`, and the multiplicative defects of `U_n`.

The ultraproduct argument narrated above is the manuscript's *printed* proof of
the same statement.  It is now also machine-checked, step by step, but it
remains conditional on one construction, so it is carried by its own node:
[[kazhdan-transport-via-printed-ultraproduct]], whose prerequisite is
[[printed-ultraproduct-ambient-for-kazhdan-transport]].  Both proofs establish
the single statement `manuscriptKazhdanTransport`.
