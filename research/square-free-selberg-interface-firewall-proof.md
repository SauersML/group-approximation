---
rg: 2
id: square-free-selberg-interface-firewall-proof
kind: route
title: Separate congruence factorization from exact endpoint bending
target: selberg-orbit-retraction-does-not-cross-square-free-basin
requires:
  - iwahori-two-triangle-torsion-normal-form
  - congruence-iwahori-endpoint-fiber-contains-core-commutant-orbits
  - modular-vertex-extension-does-not-force-congruence
---

The torsion normalization proves only that the two order-three products and
the involution are exact.  Hence it constructs exact representations of the
virtually free modular vertex group, not of a finite congruence quotient.
`modular-vertex-extension-does-not-force-congruence` supplies exact
noncongruence vertex representations, so no formal implication to the
Selberg sector exists.

Independently, the core-commutant endpoint-orbit theorem gives zero-defect
regular congruence endpoints whose relative canonical gauge has commutator
norm at least `sqrt(2)`.  Therefore no inequality can first select the
canonical endpoint representative from `(SBF1)` and then feed its edge
mismatch to Selberg.  The only valid order of operations is:

```text
authenticate congruence type modulo the exact endpoint orbit
    -> apply Selberg conditional expectation
    -> polar-complete inside the equal regular character.
```

The first arrow is the open basin theorem; the latter two are exactly the
proved regular orbit retraction.
