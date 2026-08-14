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
