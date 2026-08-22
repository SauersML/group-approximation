---
rg: 2
id: hilbert-hotel-model-is-unconditionally-non-mf-proof
kind: route
title: Build the compression core in coordinates and let the defect be everything
target: hilbert-hotel-model-is-unconditionally-non-mf
requires: []
artifacts:
  - GroupApproximation/Leavitt/HilbertHotelModelNonMF.lean
  - GroupApproximation/Leavitt/HilbertHotelEndpoint.lean
---

Machine-checked, and the reason it needs no hypothesis is that every ingredient
is a computation in the `16 x 16` frame rather than a property of a quotient.

**Compression.**  `matrixCompression_eq_scalar_form` identifies conjugation by
the Leavitt stable unit with the scalar coefficient map `a -> s_0 a t_0`, and
`Tunit_conj_cornerUnits` reads that on the rank-four corner.  So
`Cover.tau_compresses` holds: conjugation by `tauModel` carries the corner
image into itself.

**Centralization.**  `cornerUnits_commute_mark` gives `Cover.mark_commutes`.
The reason is index-disjointness of the two root *positions* --- both corner
indices are `< 4` against `(4,5)` --- and not block-disjointness as such.

**The defect is everything.**  `transported_commutator_eq_defect` computes the
marked commutator as `e_02(q)`, and
`HilbertHotel.normalClosure_defect_eq_top` (a `decide` at the root datum, with
`q != 0` from `Binary.q_ne_zero`) says that element normally generates the
model.  Hence `top_le_defectNormal`, and `top` is a nontrivial normal Kazhdan
subgroup inside the defect because the model itself is Kazhdan
(`elementaryBase_hasKazhdanPropertyT`).

**The engine.**  `QuestionTwoReduction.not_isOperatorMF_of_nontrivial_normal_kazhdan_defect`
at `modelCore` with that data gives the negative conclusion, and
`KazhdanCompressionCore.normalKazhdan_le_coronaMFResidual` gives the full
radical.  `cdeMFResidual_eq_coronaMFResidual` transports it to the literal
Carrion--Dadarlat--Eckhardt form.

## The honest boundary

Non-soficity (`Endpoint.model_not_isSofic`) comes from the same core through
the sofic side of the engine, not from a separate argument.  Finite
presentability is *not* proved here and is not implied: the model is finitely
generated (`Endpoint.model_fg`) and infinite (`Endpoint.model_infinite`), and
the whole cover layer exists because presenting it finitely is a different
problem.
