---
rg: 2
id: infinitesimal-rigidity-from-three-parts
kind: route
title: Cuspidal angle, Eisenstein angle, and norm comparison assemble the uniform first-order gap
target: iwahori-uniform-infinitesimal-rigidity
requires:
  - iwahori-cuspidal-cellular-hecke-angle
  - iwahori-eisenstein-angle
  - iwahori-cochain-petersson-comparison
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

Decompose a cocycle pair into coboundary, cuspidal and Eisenstein parts
(`iwahori-cochain-petersson-comparison`).  Coboundaries are controlled by
`(tau)`; the cuspidal part has mismatch at least `sqrt(3 - 2 sqrt 2)` times
its **cellular Hodge** size (`iwahori-cuspidal-cellular-hecke-angle`); the
Eisenstein part has a uniform transversality constant
(`iwahori-eisenstein-angle`); the fixed-complex norm comparison converts
these into the cochain-norm inequality `(UIR)`.
No unproved orthogonality under restriction is used; the proof is triangular
through the edge boundary quotient as detailed below.

Apply the edge boundary quotient first.
`iwahori-eisenstein-angle` and the uniformly bounded vertex boundary lifts
control the two Eisenstein components.  After subtracting their restrictions,
`iwahori-cuspidal-cellular-hecke-angle` controls the two interior components
directly in the cellular Hodge norm.  The
fixed-complex Hodge comparison converts these bounds back to fixed-generator
cochains.  For the remaining coboundaries, edge property `(tau)` controls the
difference of the two potentials modulo `M^B`; congruence co-density gives
`M^B=M^(V_1)=M^(V_2)` inside a congruence representation of the amalgam, so
that fixed part is harmless and one common potential proves `(UIR)`.  The
cellular norm comparison is rank-uniform because all three orbicomplexes are
fixed and all coefficient transports are unitary.
