---
rg: 2
id: multiplicity-centralization-closes-diffuse-newton
kind: route
title: Combine sparse-tail peeling, transverse code pinching, and zero-mode refinement
target: balanced-overlay-diffuse-square-function-newton
requires:
  - all-dual-unique-neighbors-contract-operator-tails
  - code-distance-upgrades-pair-energy-to-full-pinching
  - multiplicity-space-centralization-after-code-block-pinching
---

Use the all-local-dual tail recurrence to move the sparse high-residual sites
to the shortened-core repair sector.  On the diffuse complement, the
code-distance/full-pinching theorem removes all nonzero adjoint code
characters with a length-independent constant.  The remaining component is
exactly the zero-character algebra `(MSC1)`.  Applying the required
multiplicity refinement there produces one common code PVM and hence the
same-Hilbert correction demanded by the balanced Newton claim.  Errors add
in normalized squared Hilbert--Schmidt norm, with constants uniform by the
three hypotheses.

