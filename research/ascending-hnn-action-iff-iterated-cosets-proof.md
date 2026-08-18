---
rg: 2
id: ascending-hnn-action-iff-iterated-cosets-proof
kind: route
title: Identify every iterated self-image as a site stabilizer and exhaust finite telescope windows
target: ascending-hnn-action-iff-iterated-cosets
requires: []
artifacts:
  - research/artifacts/ascending-hnn-iterated-coset-solution-2026-08-18.md
  - GroupApproximation/Sofic/AscendingHNNSoficDescent.lean
  - GroupApproximation/Sofic/SoficActionCyclicExtension.lean
---

## Complete proof

Section 2 of the artifact proves both directions.

For necessity, the point `t^m Gamma` has stabilizer exactly
`alpha^m(Gamma)` inside the base, so its orbit is
`Gamma/alpha^m(Gamma)` and action soficity passes to subgroup restrictions and
orbits.

For sufficiency, given finite `F` in the telescope kernel and finite `E` in
`V/Gamma`, choose one level `Gamma_R=t^-R Gamma t^R` containing `F` and the
finitely many telescope coordinates needed to represent `E`, with `R` also
large enough to make all resulting iterate indices nonnegative.  Conjugation
by `t^R` identifies each `Gamma_R`-orbit meeting `E` with
`Gamma/alpha^m(Gamma)` for some `m`.  The assumed sofic models on those
finitely many orbits give the required local telescope model.  The repository's
cyclic-extension theorem then passes from the telescope to `V`.

No finite-index, separability, UAS, residual-finiteness, or property-(T)
hypothesis is used.
