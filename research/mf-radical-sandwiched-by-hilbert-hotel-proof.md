---
rg: 2
id: mf-radical-sandwiched-by-hilbert-hotel-proof
kind: route
title: Combine the Hilbert-hotel containment with the congruence kernel of the directly finite quotient
target: mf-radical-sandwiched-by-hilbert-hotel-radical
requires: [mf-radical-contains-hilbert-hotel-elementary-subgroup]
artifacts:
  - research/artifacts/un-open-1-hilbert-hotel-radical-2026-09-13.md
---

Derivation in artifact section 5.

The left containment is the required claim.

For the right containment, reduction modulo `hh` gives a surjection
`pi : EL_n(R) ->> EL_n(R/hh)` whose target is MF by hypothesis. So `pi` is a homomorphism from
`EL_n(R)` to an MF group, and `Rad_MF(EL_n(R)) <= ker pi`. The kernel of `EL_n(R) -> GL_n(R/hh)`
is `EL_n(R) n GL_n(R,hh)` by definition of the congruence subgroup.

The maximal MF quotient is `EL_n(R)/Rad_MF(EL_n(R))`, so the two containments bound it between
`EL_n(R)/(EL_n(R) n GL_n(R,hh)) = EL_n(R/hh)` and `EL_n(R)/EL_n(R,hh)`. The quotient of the two
bounding subgroups is `(EL_n(R) n GL_n(R,hh))/EL_n(R,hh)`, the relative `K_1`-type group of the
pair `(R,hh)` in rank `n`; when it vanishes both containments are equalities.
