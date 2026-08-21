---
rg: 2
id: infinitesimal-rigidity-from-three-parts
kind: route
title: Cuspidal angle, Eisenstein angle, and norm comparison assemble the uniform first-order gap
target: iwahori-uniform-infinitesimal-rigidity
requires:
  - iwahori-cuspidal-hecke-angle
  - iwahori-eisenstein-angle
  - iwahori-cochain-petersson-comparison
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

Decompose a cocycle pair into coboundary, cuspidal and Eisenstein parts
(`iwahori-cochain-petersson-comparison`).  Coboundaries are controlled by
`(tau)`; the cuspidal part has mismatch at least `sqrt(3 - 2 sqrt 2)` times
its Petersson size (`iwahori-cuspidal-hecke-angle`); the Eisenstein part
has a uniform transversality constant (`iwahori-eisenstein-angle`); the
norm comparison converts these into the cochain-norm inequality `(UIR)`.
Cross terms between the three parts are orthogonal in the harmonic
decomposition.
