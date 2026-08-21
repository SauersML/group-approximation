---
rg: 2
id: fixed-hodge-plus-boundary-splitting-proves-cochain-comparison
kind: route
title: Fixed-base Hodge comparison leaves only the uniform parabolic splitting
target: iwahori-cochain-petersson-comparison
requires:
  - fixed-complex-unitary-local-system-hodge-norms-are-uniform
  - iwahori-parabolic-boundary-splitting-is-uniform
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

Use one fixed compact core/cellular model for each modular vertex and edge.
The rank-independent Whitney/de Rham theorem compares its cellular quotient
norm with the analytic harmonic norm for every flat unitary coefficient
bundle.  The uniform parabolic splitting then separates the interior and
Eisenstein components without cancellation.  On the interior component this
is the Petersson norm used by `iwahori-cuspidal-hecke-angle`; on the boundary
component it is uniformly equivalent to the cusp-count residue norm used by
`iwahori-eisenstein-angle`.  Finally Selberg property `(tau)` controls the
coboundary potential modulo the commutant.  These are exactly parts (i)--(iii)
of `iwahori-cochain-petersson-comparison`.
