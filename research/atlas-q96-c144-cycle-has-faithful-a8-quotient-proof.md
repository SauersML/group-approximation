---
rg: 2
id: atlas-q96-c144-cycle-has-faithful-a8-quotient-proof
kind: route
title: Enumerate every A8 epimorphism and certify the four marked vertices
target: atlas-q96-c144-cycle-has-faithful-a8-quotient
requires:
  - atlas-q96-to-c144-cycle-is-six-generator-finite-vertex-test
artifacts:
  - experiments/atlas_a4_q96_c144_a8_quotients.g
  - research/artifacts/atlas-a4-q96-c144-a8-quotients.json
---

The verifier builds the exact finitely presented group `(Q96-C-2)` and calls
GAP's finite-target `GQuotients` algorithm with `A8`.  This returns
epimorphisms modulo target automorphisms, so the 24 maps are the complete
finite-target classification rather than a list of sampled generator tuples.

For each map it closes the images of the four marked generator subsets and
collects their orders.  The histogram is asserted literally.  It then freezes
the first all-faithful tuple, reevaluates the presentation through the
epimorphism, and checks that the six images generate a group of order `20160`.
The order equalities prove injectivity of every finite vertex because the
source vertex orders are exactly `36,96,24,144`.
