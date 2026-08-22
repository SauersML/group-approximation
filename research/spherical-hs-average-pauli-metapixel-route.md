---
rg: 2
id: spherical-hs-average-pauli-metapixel-route
kind: route
title: Collapse the Pauli marked carrier with one spherical Hilbert--Schmidt orbit frame
target: bounded-degree-entangled-agreement-pauli-metapixel
requires:
  - same-basis-rounding-interface-for-sparse-weyl-sampler
  - spherical-hs-average-bypasses-global-character-resolution
---

Use the same-basis sampler only to identify the marked Pauli seed and its
positive carrier.  Instead of recovering a global character PVM and proving
the transport energy `(ISC2)`, apply `(SHA2)--(SHA4)` to the word-generated
non-diagonal Hilbert--Schmidt orbit frame.  The fixed spherical average is
strictly contractive there, while the seed relations make its marked vector
almost invariant, so the carrier has vanishing normalized trace.

This route is intentionally parallel to
`infinite-character-actor-closes-pauli-metapixel`: it bypasses both
`infinite-character-actor-word-energy-interface` and
`one-seed-infinite-character-expansion-collapses-mark` rather than claiming
to prove either one.

