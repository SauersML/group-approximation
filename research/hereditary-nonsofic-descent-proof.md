---
rg: 2
id: hereditary-nonsofic-descent-proof
kind: route
title: Simplicity forces survival, saturation forbids collapse, the setup descends
target: hereditary-nonsofic-descent
requires: []
artifacts:
  - GroupApproximation/Sofic/HereditaryNonsoficDescent.lean
---

## Direct proof, formalized

All in `GroupApproximation/Sofic/HereditaryNonsoficDescent.lean`,
authored in the 2026-08-15 wave; the wave's closing validation build
certifies the kernel check.

- `defectNormal_eq_normalClosure_simpleSubgroup`: each displayed
  commutator `[s, iota p] = s * (iota p * s^{-1} * iota p^{-1})` is a
  product of two conjugates of simple-factor elements, so the defect's
  normal closure is at most `normalClosure(S)`; the formalized defect
  saturation (`simpleSubgroup_le_defectNormal`) gives the converse.

- `simpleSubgroup_not_le_ker`: if `S` were inside the kernel of
  `Q ->> H`, the kernel (normal) would contain `normalClosure(S)`,
  hence the defect; but `defect_surjective` maps the defect onto `Q`,
  so every element of `H` would be trivial, against `Nontrivial H`.

- `simpleSubgroup_hom_injective`: the restriction of `E -> Q -> H` to
  `S` has a normal kernel; `IsSimpleGroup` leaves bottom or top, and
  top is the previous impossibility.  `exists_simpleSubgroup_embedding`
  packages the embedding.

- `quotient_not_isSofic_of_simpleSubgroup_not_isSofic`: soficity
  passes to subgroups (`isSofic_of_injective`), so a nonsofic simple
  factor makes every nontrivial quotient nonsofic — unconditionally.

- `descendSetup`: pushes a `CompressionSetup` through a surjection;
  generation, compressing endomorphisms (chosen through preimages,
  with the defining equation independent of the choice), the
  centralizing relations, and finiteness data all descend by proof;
  only the two injectivity constraints are consumed as hypotheses.

- `HereditaryNonsoficData` extends `NonsoficCriterionData` by exactly
  those two retention fields; `quotient_not_isSofic` then applies the
  formalized criterion `not_isSofic_of_not_isLEF` to the descended
  setup, with property (T) of `H` inherited through the surjection and
  the non-LEF witness unchanged.  `hereditary_package` combines this
  with the already-formalized hereditary full-radical and non-MF
  theorems.

The route is complete as a reduction theorem: what it does NOT claim
is an unconditional discharge of the retention fields, which is part
of the small-cancellation construction itself (the same boundary as
`DefectRoutingData`).
