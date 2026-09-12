---
rg: 2
id: boone-base-group-two-generator-one-relator-proof
kind: route
title: Two easy maps, each easy for a different reason, checked on generators
target: boone-base-group-two-generator-one-relator
requires: []
artifacts:
  - GroupApproximation/Computability/BooneGroupPresentation.lean
---

## Direct proof, machine-checked

**Forward** (`toBase`) is `PresentedGroup.toGroup` applied to
`genMap : Fin 3 -> BaseGroup`, `t |-> tGen`, `x |-> xGen`, `y |-> yGen`.  Its
only obligation is that the relator dies, which holds because the acting group
is `Z^2` (`genMap_rel`, off `sh_comm`).

**Backward** (`ofBase`) is `SemidirectProduct.lift fLeft fRight lift_compat`.
The free factor goes to conjugates of `t`, matching Simpson's
`t(a,b) = x^{-a} y^{-b} t x^{a} y^{b}` (`fLeft_of`); the acting factor goes to
`x^u y^v` (`fRight`).  That `fRight` is a homomorphism at all is where the
relation is used, through `Commute.zpow_zpow` on `commute_XY`; `lift_compat`
is the conjugation identity the semidirect-product lift demands.

**The two composites** are checked generator by generator:
`PresentedGroup.ext` in one direction, `SemidirectProduct.hom_ext` in the
other.  `presentedEquiv` bundles them.

No hypothesis, and no appeal to any normal-form theorem for one-relator
groups.
