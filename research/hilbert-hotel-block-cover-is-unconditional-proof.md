---
rg: 2
id: hilbert-hotel-block-cover-is-unconditional-proof
kind: route
title: Both records are inhabited, so the endpoint theorem loses its arguments
target: hilbert-hotel-block-cover-is-unconditional
requires: []
artifacts:
  - GroupApproximation/Leavitt/HilbertHotelCoverBlock.lean
  - GroupApproximation/Leavitt/HilbertHotelEndpoint.lean
---

Machine-checked.  The chain is short because every step is already in the
kernel-checked tree.

**The generic endpoint.**  `hilbertHotel_finitelyPresented_endpoint` takes a
`CoverInputs` and a `CoverBlockResiduals` and returns the whole profile ---
finite presentability, countability, nontriviality, property `(T)`, corona
invisibility of every element, and the negative conclusion.

**The first record is inhabited.**  `blockCoverInputs` is
`Classical.choice Cover.coverInputs_nonempty`, and
`Cover.coverInputs_nonempty` is unconditional: its one field
`exists_conjProduct` comes from `model_exists_conjProduct`, which is the
generic closure induction `ConjWord.exists_conjWord` run against
`normalClosure_defectModel_eq_top` and `freeToModel_surjective`.  The defect
normally generates the model by `HilbertHotel.normalClosure_defect_eq_top`,
which is `decide`-backed at the root datum.

**The second record is inhabited.**  `coverBlockResiduals` supplies four
model-level facts, all proved and none of them about the cover:
`Cover.tau_compresses` and `Cover.mark_commutes` (the two compression clauses,
read off `Tunit_conj_cornerUnits` and `cornerUnits_commute_mark`),
`Cover.cornerGenerator` as the witness, and
`Cover.transported_commutator_eq_defect` as the defect computation.

**Composition.**  `CoverBlock.hotelGroup_endpoint` is the generic endpoint at
those two, so it has no arguments; the existence form
`exists_finitelyPresented_kazhdan_full_mf_radical` packages it, and
`Endpoint.hotelGroup_cdeMFResidual_eq_top` upgrades the corona statement to the
literal Carrion--Dadarlat--Eckhardt residual.

## Why this is not the one-block cover restated

`CoverGroup_2` is a different group from `CoverGroup C`: its presentation
carries the corner generators, so the Kazhdan source has a homomorphism into it
and its `core` field is constructible.  The one-block record's `core` field is
not, and the route recorded at
[[one-block-cover-residuals-are-structurally-unreachable]] is the reason.  No
theorem here discharges a one-block field; the construction sidesteps it.
