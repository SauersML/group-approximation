---
rg: 2
id: fresh-renewal-via-gauge-doubled-derived-reset
kind: route
title: Preserve logical BCS words with gauge shares and renew only their private gauges
target: fresh-selector-renewal-after-symplectic-chart-reset
requires:
  - gauge-doubling-gives-selector-flip-symmetries
  - weyl-derivative-reset-preserves-schur-spin-scale
  - derived-lifted-gauge-reset-spin-bridge
---

Gauge-double the finitely many selector variables in each Fanizza context.
Compile each predicate as a function of the logical products `A_xB_x`. The
pair-flip directions are nonzero, so the finite-field compiler gives an
invertible derivative in every such direction. Apply the Weyl derivative
cell only to the private gauge coordinates. It fixes the logical products
pointwise, and the finite gauge-orbit representation supplies exact marked
completeness even when the original representation is not gauge covariant.

Use the derived lifted bridge to install the next context's private gauges at
the same spin scale. Shared logical variables are carried literally, while
old and fresh gauge choices are transverse; hence no extra commutator between
distinct logical BCS variables is imposed. Fixed arity and a fixed predicate
menu bound the incidence and exactification constants.

