# Non-MF impact results: formal status

Date: 2026-08-14

This note records the trust boundary for the strongest consequences around
`non_mf_groups_exist.tex`.  A result is called **closed** below only when the
advertised Lean declaration has no hypothesis standing in for a construction,
property `(T)`, soficity, MF-ness, or a literature theorem.

## Closed endpoints

The release-facing collection is
`GroupApproximation/Endpoint/NonMFImpact.lean`.

- `NonMFImpact.literal_sixGenerated_finitelyPresented_nonMF` proves that the
  literal group is finitely presented, has group rank at most six, and is not
  operator-MF.
- `NonMFImpact.literal_nonempty_clopen_nonMF_cylinder` proves that the exact
  rank-eight finite cylinder is nonempty and clopen and contains only non-MF
  groups.
- `NonMFImpact.witness_locallyFinite_MF_kernel_nonMF_total` proves that the
  concrete Clifford witness is finitely generated and non-MF, while its
  canonical lamp kernel is locally finite, LEF, sofic, and operator-MF.
- `NonMFImpact.affineBase_residuallyFinite_sofic_MF` proves internally that
  the concrete affine matrix base is residually finite, sofic, and
  operator-MF.  The proof reduces its explicit integral matrix realization
  modulo finite moduli; it does not assume Mal'cev's theorem.
- `NonMFImpact.scalingFamily_finitelyPresented_nonMF` proves the whole
  scaling family: for every integer `m >= 2`, the corresponding group is
  finitely presented and non-MF.
- `NonMFImpact.cyclicBase_exactModel_obstruction` proves that the cyclic
  marked sign survives, dies in every finite image, and prevents both the
  literal cyclic group and its realized Clifford quotient from being LEF;
  the realized quotient is not residually finite.
- `NonMFImpact.operatorMF_not_closed_under_quotients` supplies a concrete MF
  group with a non-MF quotient.

The logical and topological obstruction is also exposed separately by
`LiteralUniversalHorn.manuscriptLiteralUniversalHorn` and
`LiteralMarkedCylinder.literal_nonempty_clopen_nonMF_cylinder`.

## Closed reusable mechanisms

These theorems have ordinary mathematical parameters, but assume no external
result and are used to discharge concrete endpoints:

- `isSofic_of_every_finset_mem_sofic_subgroup` and
  `isSofic_of_increasing_union`: local and increasing-union permanence for
  soficity.
- `isSofic_finiteKernel_semidirectProduct`: a direct Hamming-model proof for
  split extensions with finite normal factor.
- `CliffordLamp.finite_cliffordLamp` and
  `CliffordLamp.isLocallyFiniteGroup_cliffordLamp`: finite-site finiteness and
  arbitrary-site local finiteness of the presented Clifford lamp group.
- `generalLinearGroup_int_residuallyFinite`: residual finiteness of integral
  general linear groups by explicit modular reduction.
- `ExplicitIntegralLinearModel.gammaBar_residuallyFinite`: the closed
  specialization to the literal affine base.

## Not yet a closed Lean endpoint

The manuscript's finite-coset-tower proof that the **total** Clifford witness
is sofic is not yet represented by a premise-free Lean theorem.  The pieces
above establish the finite lamp groups, split finite-kernel permanence,
directed-union permanence, and residual finiteness of the concrete base.  The
remaining formal work is the concrete tower/dilation identification together
with the final cyclic/amenable-quotient permanence step.

Consequently, the following prose consequences must not receive an `EXACT`
badge until that endpoint is completed:

- the total witness is sofic;
- sofic does not imply MF via this witness;
- MF is not closed under extensions via this witness;
- the simple sofic envelope has full MF radical.

Their mathematical proofs may cite the stated Elek--Szabó permanence and
simple-envelope theorems, but those citations are outside the current closed
Lean trust surface.  No conditional Lean facade should be used as a substitute.

## Presentation count

Lean proves that six named elements generate the literal group and hence that
its rank is at most six.  The thirty-two-relator Tietze presentation is
currently a human syntactic calculation.  The manuscript therefore separates
the machine-checked rank statement from the unbadged relator-count statement.
