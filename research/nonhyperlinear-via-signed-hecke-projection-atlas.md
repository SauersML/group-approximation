---
rg: 2
id: nonhyperlinear-via-signed-hecke-projection-atlas
kind: route
title: Pull the canonical signed-corner trace back through the compatible BCS atlas
target: non-hyperlinear-group
requires:
  - mipstar-bcs-tracial-nonru-exists
  - signed-hecke-compatible-projection-atlas-for-nonce-bcs
  - bcs-corner-model-is-a-compatible-projection-atlas
  - nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear
  - algebraic-bcs-corner-has-relator-energy-decoder
  - nontrivial-finite-type-corner-kills-scalar-characters
---

The atlas equations give the unital homomorphism `(SHA2)` by
`bcs-corner-model-is-a-compatible-projection-atlas`. Its corner unit has
positive canonical trace by the finite-type formula `(FTC2)`. If `Gamma`
were hyperlinear, `nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear`
would turn that canonical corner trace into a Connes-embeddable tracial state
on `A(B)`, contradicting `mipstar-bcs-tracial-nonru-exists`.

This route is direct trace promotion. It bypasses the stronger and unrelated
task of making the corner trace unique, and it bypasses every approximate
matrix decoder: the exact algebraic atlas itself forces the canonical group
trace to witness the forbidden BCS profile.

Equivalently, the final requirement gives a finite-coordinate proof: every
atlas identity has a fixed relator certificate, and the positive canonical
`q` carrier converts the robust BCS gap into a uniform defining-relator
energy floor.  Thus no independent coefficient-to-word payment remains once
the compatible algebraic atlas is constructed.
