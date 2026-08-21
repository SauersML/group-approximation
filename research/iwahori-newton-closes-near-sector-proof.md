---
rg: 2
id: iwahori-newton-closes-near-sector-proof
kind: route
title: A normal-geodesic Taylor estimate closes each smooth multiplicity stratum
target: iwahori-newton-closes-near-sector
requires:
  - iwahori-uniform-infinitesimal-rigidity
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

On a fixed torsion-multiplicity stratum, take a nearest compatible point and
the normal minimizing geodesic to the given pair.  Uniform infinitesimal
rigidity bounds the first derivative of the compatibility map below on this
normal direction.  Fixed word length bounds the second derivative in
normalized Hilbert--Schmidt norm.  Taylor's formula gives
`def >= sigma_0 D-(L/2)D^2`, hence `D<=2 def/sigma_0` for
`D<=sigma_0/L`.  No right inverse or surjectivity assertion is used.

The argument is intentionally stratumwise.  A separate theorem is required
to reconcile torsion spectral multiplicities whose normalized rank
difference tends to zero with dimension.
