---
rg: 2
id: ghb7-is-not-flexibly-hs-stable
kind: claim
title: GHB_2(7) is not flexibly Hilbert--Schmidt stable
distinct_from:
  ghb7-flexibly-hs-stable: that is the stability premise of the route to non-hyperlinear-group; this is its negation, which would close that route
  rf-kazhdan-group-not-flexibly-hs-stable: that proves instability of the affine symplectic group, which contains Z^2 and has a non-torsion class on the whole group; this asks instability of a hyperbolic Kazhdan group whose real degree-two cohomology vanishes and appears only on finite-index subgroups
---

**OPEN.** `G = G_{HB_2}(7)` (`cckw-ghb2-kms-group-structure`) is not flexibly HS stable in Dogon's
sense (arXiv:2211.10492v3, Definition 1.2). Equivalently
(`triangle-of-finite-groups-hs-stability-is-edge-matching`,
`triangle-edge-matching-reduces-to-one-edge-holonomy`), `ghb7-one-edge-holonomy-absorption` fails.

**Why it matters.** It is the negation of `ghb7-flexibly-hs-stable`. If established, the GHB_2(7)
stability route to `non-hyperlinear-group` is dead, and the graph should mark
`ghb7-flexibly-hs-stable` refuted.

**Known necessary shape.**
- `H^2(G;R) = 0` (`ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2`), so no central
  `Z`-extension of `G` itself has finite abelianization. A central-cover witness must live on a
  finite-index subgroup.
- A witness cannot be detected by invariant-fraction counts of vertex and edge groups
  (fence bullets on `ghb7-flexibly-hs-stable` and `ghb7-one-edge-holonomy-absorption`).
