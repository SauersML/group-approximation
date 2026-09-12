---
rg: 2
id: spherical-near-perfect-local-package-route
kind: route
title: Assemble the spherical near-perfect packing package
target: spherical-near-perfect-local-package
requires:
  - spherical-relation-quadruple-counts
  - spherical-fixed-order-cap-codegrees
  - spherical-collapsed-relation-target-abundance
---

The three prerequisites are exactly the four bullets in the claim:
`spherical-relation-quadruple-counts` includes the one-colour degree estimates
used in its proof and supplies four-slot degrees/repeated-slot codegrees;
`spherical-fixed-order-cap-codegrees` supplies every fixed distinct-word
intersection estimate; and `spherical-collapsed-relation-target-abundance`
supplies the literal `l=m` reservoir on good relation edges.  Each statement
is simultaneous over a fixed finite table after choosing the cloud size large
enough, so their finite intersection has probability tending to one.
