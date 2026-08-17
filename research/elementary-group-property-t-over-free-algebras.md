---
rg: 2
id: elementary-group-property-t-over-free-algebras
kind: claim
title: Property (T) for rank-three elementary groups over free algebras on a finite field, proved in the development
distinct_from:
  universal-leavitt-el4-nonsofic: That is the nonsoficity endpoint, which consumes this as one of its three inputs; this is a property-(T) statement with no soficity in it.
  one-sided-compression-nonsofic-criterion: That is the criterion, which takes property (T) as a hypothesis on two groups; this is what discharges that hypothesis for the Leavitt lane.
artifacts:
  - GroupApproximation/PropertyT/FiniteFieldElementaryPropertyT.lean
  - GroupApproximation/PropertyT/FiniteTypeCharacteristicTwoPropertyT.lean
  - GroupApproximation/PropertyT/A2Kazhdan.lean
  - GroupApproximation/PropertyT/FreeRootPlaneMass.lean
  - GroupApproximation/PropertyT/ClassTwoApproximation.lean
---

ESTABLISHED, and proved here rather than quoted.
`PropertyT/FiniteFieldElementaryPropertyT`:

* `controlSet_isKazhdanPair` -- an explicit finite Kazhdan pair for `EL_3` over
  a free algebra on a finite coefficient field, the control set being every
  scalar multiple of the unit and every free generator in each of the six
  elementary roots;
* `freeElementary_hasKazhdanPropertyT` and
  `finiteFieldElementaryThree_hasKazhdanPropertyT` -- the resulting property
  `(T)`.

`PropertyT/FiniteTypeCharacteristicTwoPropertyT` descends it: every finite-type
`ZMod 2`-algebra is a quotient of a free algebra on a finite type, so the
kernel-checked free-algebra theorem transfers to its rank-three elementary
group.

This is the Ershov--Jaikin-Zapirain input in the form the development needs,
proved rather than transcribed -- the `LITERATURE_INPUT` roster of
`scripts/Audit.lean` is empty.

## What the finiteness of the field costs

It is exactly the reach of the argument, and it is why
[[d-ary-leavitt-groups-nonsofic-over-finite-fields]] stops at finite fields:
the integral case, property `(T)` for `EL_3(Z<X>)` and hence nonsoficity of
`EL_4(L_Z(1,2))`, is not formalized anywhere in the development. The
mass/energy estimates behind the Kazhdan pair (`A2MagicEnergy`,
`FreeRootPlaneMass`, `A2ClassTwoOrthogonality`) are stated over a finite
coefficient field throughout.

Rank four comes from rank three by the explicit Leavitt rank equivalence, not
by re-running the estimate; that transport is `Leavitt/UniversalPropertyT`.
