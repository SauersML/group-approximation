---
rg: 2
id: gkmp-hnn-form-closes-compiler
kind: route
title: GKMP closes only the outer central detector after the inner HNN tower is MF and its edge is separable
target: mf-safe-finite-presentation-compiler
requires:
  - gkmp-amalgam-product-mf-permanence
  - gkmp-closes-fp-mf-completeness-modulo-hnn-and-separability
  - modular-machine-boone-group-is-mf
  - bidirectional-hnn-bridge-trivial-value-is-residually-finite
---

For the actual compiler in `Higman/InjectedCompilerTower.lean`, first prove
MF permanence through the finite `tau_j` family and the `d` and `sigma`
basis-to-basis HNN edges.  Then prove that the transported conjugate detector
subgroup is separable in that completed inner tower.  Under exactly those
hypotheses, GKMP Theorem 1.1 with `L = Z` proves that the final central HNN
detector is MF.

Neither hypothesis is currently discharged.  In particular,
Chiodo--Vyas does not supply a virtually-special ambient, and separability in
an earlier ambient would not automatically imply separability after the HNN
tower.  For the older graph-rope output
`<G x C, s | s(l,1)s^-1=(l,phi(l))>`, an HNN form of GKMP or a proved
embedding into a GKMP product-amalgam would still be needed; Theorem 1.1
itself supplies neither.

This is an alternate route through the older injected machine tower, not a
dependency of the established Mikhailova/graph-witness compiler. The latter
closes its different asymmetric edge via
[[twisted-hnn-mf-permanence-with-corona-conjugator]].
