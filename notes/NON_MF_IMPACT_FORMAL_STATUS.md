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
- `NonMFImpact.witness_sofic_nonMF` proves, with no inputs, that the same
  concrete finitely generated witness is sofic and not operator-MF.
- `NonMFImpact.witness_hyperlinear_nonMF` proves, again for that concrete
  witness and with no inputs, that hyperlinearity does not imply MF.
- `NonMFImpact.witness_sofic_hyperlinear_nonMF` packages finite generation,
  soficity, hyperlinearity, and failure of MF in the single closed theorem
  cited by the manuscript.
- `NonMFImpact.witness_reducedGroupCStar_stablyFinite_nonMF` proves that the
  witness's reduced group C-star algebra is separable, has its canonical
  faithful trace, is stably finite in every finite matrix amplification, and
  is not MF.  Exactness is the only part of the manuscript's corresponding
  paragraph outside the present formal vocabulary.
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
- `NonMFImpact.literal_uniform_operatorNorm_obstruction` supplies one finite
  test set and one positive defect threshold, uniform in matrix dimension,
  that force the literal mark within operator norm `< 1` of the identity.
  This is a compactness theorem; it does not yet compute the test set or
  threshold from the rational P13 certificate.
- `NonMFImpact.finiteNormal_obstruction_is_trivial_in_torsionFree_groups`
  proves that every finite subgroup of a torsion-free group is trivial,
  precisely delimiting the finite-normal method.
- `NonMFImpact.sofic_nonMF_is_hyperlinear_nonMF` formalizes the general
  implication used to pass from a sofic non-MF witness to a hyperlinear
  non-MF witness.

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
- `isSofic_int_semidirectProduct`: a direct truncated-level proof that a
  split extension of a sofic group by the integers is sofic.
- `isSofic_telescope`: soficity of the mapping telescope of an injective
  endomorphism of a sofic group.
- `isSofic_semidirectProduct_of_invariant_finite`: a local criterion that
  assembles finite invariant kernel windows acted on by sofic subgroups.
- `MappingTelescopeFiniteOrbits.finite_verticalLevel_orbit`: finite-index
  compression makes every telescope level orbit on the marked coset space
  finite, via commensuration and orbit--stabilizer.
- `CliffordLamp.exists_finite_invariant_clifford_subgroup`: finite site
  orbits place any finite Clifford window in a finite invariant subgroup.
- `SoficMarkedCompression.isSofic_ambient`: the intrinsic combination of
  the telescope-orbit, invariant-kernel, reassociation, and integer-extension
  arguments.
- `CliffordLamp.finite_cliffordLamp` and
  `CliffordLamp.isLocallyFiniteGroup_cliffordLamp`: finite-site finiteness and
  arbitrary-site local finiteness of the presented Clifford lamp group.
- `generalLinearGroup_int_residuallyFinite`: residual finiteness of integral
  general linear groups by explicit modular reduction.
- `ExplicitIntegralLinearModel.gammaBar_residuallyFinite`: the closed
  specialization to the literal affine base.

## Remaining formal boundary

The total witness is now a premise-free closed Lean endpoint.  In particular,
the manuscript's concrete separation "sofic does not imply MF" may carry an
exact badge.  The reusable proof is intrinsic: it does not posit an auxiliary
tower and then leave an isomorphism to the concrete witness unproved.

Literature-dependent consequences such as the simple sofic envelope still
remain outside the closed Lean surface unless their cited permanence theorem
has itself been formalized.  No conditional facade is used in their place.

The exact-radical computation
`Rad_MF(E) = {1,w}` is also open: the development proves the universal
factorization criterion reducing it to operator-MF of `E / ⟨w⟩`, but does
not construct the genuinely approximate models that quotient would require.
The effective quantitative strengthening is likewise open: the closed
uniform theorem above gives existential `δ` and `F₀`, not a numerical modulus
on the displayed relators.

There is currently no definition of exact C-star algebras or exact groups in
the imported mathlib surface.  Thus the exactness corollary for the Clifford
witness would require substantial new operator-algebra infrastructure; it is
not represented by a conditional facade or a literature axiom.

Their mathematical proofs may cite the stated Elek--Szabó permanence and
simple-envelope theorems, but those citations are outside the current closed
Lean trust surface.  No conditional Lean facade should be used as a substitute.

## Presentation count

Lean proves that six named elements generate the literal group and hence that
its rank is at most six.  The thirty-two-relator Tietze presentation is
currently a human syntactic calculation.  The manuscript therefore separates
the machine-checked rank statement from the unbadged relator-count statement.
