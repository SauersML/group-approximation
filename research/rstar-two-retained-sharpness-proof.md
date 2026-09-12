---
rg: 2
id: rstar-two-retained-sharpness-proof
kind: route
title: Odd parity reconstructs the omitted coordinate from any other three
target: rstar-two-retained-selector-threshold-is-sharp
requires:
  - rstar-fano-ghost-affine-hull-criterion
---

For `K` of size three, two odd-parity words agreeing on `K` agree on the
fourth coordinate, so the projection is injective.  It therefore maps the
seven words of `R_*` to seven distinct patterns.  Give every word positive
weight in the diagonal algebra `C^7`.  If the three retained observables are
unchanged, their joint minimal projections are exactly these seven atoms.
On each atom odd parity forces the omitted eigenvalue, leaving no replacement
choice.  The support is still `R_*`, whose ghost translation is every
nonzero point of `F_2^3` and contains all seven Fano lines.  The prerequisite
therefore says it is not cap-supported.

