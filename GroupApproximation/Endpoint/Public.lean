import GroupApproximation.Endpoint.MainResults
import GroupApproximation.Endpoint.ManuscriptStatements
import GroupApproximation.Sofic.ChosenNonMFTheorem
import GroupApproximation.Sofic.FiniteNormalCompressionObstruction
import GroupApproximation.Sofic.NormMFUniversalCorona
import GroupApproximation.Sofic.NormMFCoronaRadical
import GroupApproximation.Sofic.FiniteNormalCoronaObstruction
import GroupApproximation.Sofic.OperatorMFPositiveControls
import GroupApproximation.Sofic.OperatorMFIncreasingDimensions
import GroupApproximation.Sofic.MarkedGroupWordBall
import GroupApproximation.Sofic.MarkedMFClosed
import GroupApproximation.Sofic.OperatorMFQuotientNonclosure
import GroupApproximation.Sofic.OperatorMFFreeProductConsequences
import GroupApproximation.Sofic.NormMFPrintedConsequences
import GroupApproximation.Sofic.NormMFResidualExactQuotient
import GroupApproximation.Analysis.FaithfulTracialMatrix
import GroupApproximation.Analysis.ProperIsometryFromCompression
import GroupApproximation.Computability.OperatorMFMarkovWitness
import GroupApproximation.Computability.MarkovMFConsequences
import GroupApproximation.Computability.CStarRecognitionConsequences
import GroupApproximation.Criterion.CompressionCentralizerDefect
import GroupApproximation.Criterion.FiniteDimensionalKill
import GroupApproximation.Monsters.CliffordAlgebraLamp
import GroupApproximation.Monsters.ExplicitLinearModel
import GroupApproximation.Monsters.AffineSL3Doubling
import GroupApproximation.Monsters.LiteralCyclicCalibration
import GroupApproximation.Sofic.CompressionDefectSquare
import GroupApproximation.Sofic.IntrinsicCompressionDefect
import GroupApproximation.Sofic.LiteralFiniteDimensionalObstruction
import GroupApproximation.Sofic.LiteralNonMFLinearWitness
import GroupApproximation.Sofic.LiteralNonMFPresentation
import GroupApproximation.Sofic.MarkedGroupTopology
import GroupApproximation.Sofic.LiteralMarkedCylinderTopology
import GroupApproximation.Sofic.LiteralPresentationRadius
import GroupApproximation.Sofic.LiteralUniversalHorn
import GroupApproximation.Sofic.NormalKazhdanCompressionObstruction
import GroupApproximation.Sofic.TensorPowerAmplification
import GroupApproximation.Covers.KazhdanCover
import GroupApproximation.Kazhdan.ShalomFinitePresentation
import GroupApproximation.Kun.KunDecomposition
import GroupApproximation.KunThom.KunThomTheorem
import GroupApproximation.KOne.RefineLoopDischarge
import GroupApproximation.KOne.ClassicalKOne
import GroupApproximation.KOne.FactorizationCertificate
import GroupApproximation.Kazhdan.KazhdanTextbook
import GroupApproximation.Kazhdan.FixedSpaceStabilizer
import GroupApproximation.Kazhdan.FixedSpaceDefect
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration

/-!
# The public results

The library is organized by the order the mathematics was discovered, which is
not the order anyone should read it in.  This module is the reading path: the
declarations a referee actually needs, each named against the theorem of
`nonsofic_groups_exist.tex` or `non_mf_groups_exist.tex` it establishes, and
nothing else.  Follow the imports downward from here.

Nothing is proved in this module.  It re-exports, so that `#check` on any name
below lands on the real statement and its module.

The full statement-by-statement correspondence is `docs/CLAIM_MAP.md`,
generated from the manuscript's margin notes; this module is the short list.

## The headline

* `nonsofic_groups_exist` -- a nonsofic group exists.  Theorem A.
* `countable_nonsofic_groups_exist` -- a countable nonsofic group exists: the
  historical headline, with the same witness.
* `countable_group_without_essentiallyFreeNearAction_exists` -- the negative
  answer to Pestov's Question 5.3, as the formal corollary of the previously
  known Elek--Szabó characterization and the countable nonsofic witness.
* `universalLeavittEL4_not_isSofic` -- the explicit witness: `EL₄` over the
  universal binary Leavitt algebra `L_{𝔽₂}(1,2)`.
* `ambient_full_profile` -- that group is countable, finitely generated,
  infinite, Kazhdan, and not sofic.
* `exists_finitelyPresented_nonsofic_group` -- Theorem C, first assertion.
* `exists_infinite_finitelyPresented_nonsofic_ambient_cover` -- and it covers
  the explicit ambient group.

## The operator-norm MF obstruction

* `ChosenNonMFTheorem.mark_normMFInvisible` -- the nontrivial marked word in
  the noncomputably chosen Shalom-cover witness is
  killed by every homomorphism to every norm-matrix ultraproduct.
* `ChosenNonMFTheorem.chosenFinitelyPresented_not_isWeakMF` -- the chosen
  finitely presented marked group is not local weak-MF.
* `ChosenNonMFTheorem.chosenFinitelyPresented_not_isOperatorMF` -- the
  same conclusion stated for the standard cofinite norm-matrix-corona
  predicate, rather than the local weak-MF predicate.
* `ChosenNonMFTheorem.exists_countable_not_isWeakMF` and
  `ChosenNonMFTheorem.exists_finitelyPresented_not_isWeakMF` -- the two
  headline existence forms.
* `KazhdanCompressionCore.finiteNormal_le_normMFResidual` -- the stronger
  Clifford-free criterion: every finite normal subgroup contained in the
  compression-defect normal closure is invisible to all norm-matrix
  ultraproduct homomorphisms.
* `KazhdanCompressionCore.not_isOperatorMF_of_finiteNormal_le_defect` -- the
  same criterion as a direct obstruction to the standard cofinite-corona
  definition of operator MF.
* `isOperatorMF_iff_normMFResidual_eq_bot` and
  `normMFQuotient_isOperatorMF` -- the universal norm-MF quotient is itself
  operator MF, and residual triviality exactly characterizes operator MF for
  countable groups.
* `coronaMFResidual_eq_normMFResidual` and
  `finiteNormal_le_normMatrixCoronaKernel` -- the same statements in the
  manuscript's intersection-of-corona-kernels language, using the
  unitary-sequence presentation documented in `Sofic/OperatorMF`.
* `isOperatorMFIncreasing_iff` -- the arbitrary positive dimension sequences
  used internally are equivalent to the strictly increasing convention in
  Carrión--Dadarlat--Eckhardt.
* `MarkedGroupSpace.isClosed_operatorMFLocus` -- operator-MF groups form a
  closed locus in each fixed-rank marked-group space, with a finite word-ball
  cylinder witnessing every failure.
* `ChosenNonMFTheorem.not_every_group_isOperatorMF` -- the direct negative
  answer to the universal operator-MF assertion.
* `not_isOperatorMF_coprod_left` -- a non-MF factor forces the entire group
  free product to be non-MF; the unconditional chosen witness gives a
  finitely presented example after free product with `ℤ`.

## The literal eight-generator boundary

The paper's displayed group is formalized separately from the unconditional
Shalom-cover witness.  The declarations below expose only its verified
algebraic boundary.  No conditional operator-MF endpoint for the literal
group is part of the Lean API.

* `LiteralNonMFPresentation.literal_algebraic_package` and
  `LiteralNonMFLinearWitness.literal_mark_ne_one` -- the displayed finite
  presentation, its relations, and a genuine nontrivial marked involution.
* `LiteralFiniteDimensionalObstruction.literal_finiteDimensional_rep_not_injective`
  -- every finite-dimensional linear representation of the literal group is
  nonfaithful.
* `LiteralUniversalHorn.literalMarkedGroup_not_satisfies_literalQuasiIdentity`
  -- the canonical literal tuple unconditionally falsifies the printed finite
  quasi-identity.  No validity claim for operator-MF targets is asserted.
* `LiteralPresentationRadius.relator_wordLength_le_34` -- a kernel-checked
  finite-radius bound for every printed relator.
* `LiteralMarkedCylinder.literalCylinder_isClopen`,
  `LiteralMarkedCylinder.cylinder_relator_eq_one`, and
  `LiteralMarkedCylinder.cylinder_markedWord_ne_one` -- the exact nonempty
  rank-eight clopen cylinder, with every printed relation retained and the
  obstruction word surviving throughout it.

## Consequences and reusable obstruction APIs

* `not_injective_of_coronaMFInvisible` and
  `KazhdanCompressionCore.finiteNormal_uniform_invisibility` -- portability
  and uniform killing of the obstruction.
* `existsUnique_quotient_factorization_to_normMatrixCorona` -- exact quotient
  factorization in the cofinite-corona language.
* `MarkovMFConsequences.operatorMF_recognition_undecidable` -- the generic
  computability reduction, conditional on an explicitly supplied computable
  Adian--Rabin transformation and its correctness proof; no such external
  transformation is postulated by the library.
* `OperatorMFMarkovWitness.exists_finitelyPresented_forbidden_subgroup` --
  the unconditional group-theoretic positive/negative Markov witness used by
  such a reduction; this does not manufacture the missing syntactic
  Adian--Rabin transformation.
* `CStarRecognitionConsequences.all_groupCStar_recognition_undecidable` -- the
  analogous five-predicate C-star recognition package, still conditional on
  explicit computable Adian--Rabin reductions and semantic predicate data;
  no group-C-star API or reduction is smuggled in as a theorem.
* `ProperProjectionCompression` -- the one-sided compression API, including
  its proper isometry, failure of stable finiteness, and obstruction to a
  faithful tracial state.
* `FixedSpaceStabilizer.compressionGroup_le_stabilizer` -- the exact subgroup
  closure step propagating fixed-sector stabilization from one-sided
  compressors to the group they generate.
* `AffineSL3Doubling.doubling_package` -- the semantic affine group used by
  the printed construction, with injective doubling, index-eight image, and
  an explicit translation outside that image.  This does not assert that the
  literal six-generator presentation is isomorphic to the semantic group.
* `MarkedGroupSpace.tendsto_iff_eventually_relation` and
  `exists_opTensorPow_norm_sub_one_gt_one_of_diagonal_gap` -- the fixed-rank
  marked-group topology and the operator-norm tensor amplifier used by the
  marked-limit program.
* `LiteralCyclicCalibration.mark_ne_one` and
  `LiteralCyclicCalibration.finiteDimensional_kill` -- the literal cyclic
  comparison presentation has a surviving marked involution although every
  exact finite-dimensional representation kills it.  Its corona-survival
  theorem keeps operator-MF of the concrete Clifford target as an explicit
  premise; it is not advertised as a formal proof of all of manuscript
  Theorem C.

## One endpoint per printed theorem

The declarations above are the ones the proofs actually produce; their types are
the library's own vocabulary.  `Endpoint/ManuscriptStatements` restates the
headline theorems so that a single name carries a single *printed* statement,
which is what a referee checking the paper against the library wants.

* `theoremB_exact` -- Theorem B, all clauses at once: the four-property profile
  of `Lˣ`, of every `GL_r(L)` (`r ≥ 1`) and of every `EL_r(L)` (`r ≥ 2`),
  together with `GL_r(L) = EL_r(L)` for `r ≥ 2` and, for every ordered complete
  leaf set, the printed formula for the specific isomorphism `theoremB_Theta`.
  Naming that map rather than asserting `Nonempty (GL_r(L) ≃* Lˣ)` is what
  makes the one type carry equation `eq:Theta-main` as well.  The Panorama
  theorem `thm:allranks` is this same statement under the manuscript's other
  name; one declaration serves both.
* `theoremB_Theta`, `theoremB_Theta_apply` -- the isomorphism `Θ_C` of equation
  `eq:Theta-main` and its printed formula `(a_ij) ↦ ∑ αᵢ a_ij αⱼ*`.
* `theoremC_exact`, `theoremC_covers_theoremB_groups` -- Theorem C's final
  assertion: an infinite finitely presented Kazhdan nonsofic group surjecting
  onto `Lˣ`, and hence onto every group of Theorem B.
* `theoremD_subgroups` -- Theorem D in the printed subgroup form, with actual
  `Subgroup G` data rather than the `CompressionSetup` interface, and with the
  printed hypotheses and no others: `G`'s finite generation and `G`'s
  countability are both derived rather than assumed, the latter from property
  `(T)` by `GeneralCornerTheorem.countable_of_hasKazhdanPropertyT`.
* `cor_fgring_printed` -- Corollary `cor:fgring` verbatim: every `m ≥ 2`,
  `n = m + 1`, the printed memberships `u, z ∈ EL_n(A)` as hypotheses, and all
  four printed conclusions about `EL_n(A)`.
* `cor_fgring_exact`, `cor_fgring_countableFree` -- the same corollary with the
  memberships discharged instead of assumed, at rank four and then at every
  rank `≥ 2`, and with no countability hypothesis (`countable_of_finiteType`).
* `ManuscriptProfile` -- the four clauses "infinite, finitely generated,
  property `(T)`, not sofic" that Theorems A, B and `cor:fgring` all end in.

## `K₁` as a group rather than as a membership

* `binaryLeavittStableUnits_eq_top` -- the `K₁` chain in subgroup form.
* `BinaryLeavittWhiteheadK1` -- the quotient `Lˣ / stableUnits`, which is `K₁`
  in Whitehead form; `binaryLeavittWhiteheadK1_subsingleton` proves it trivial.
* `ClassicalGLColim`, `elementaryColim`, `BinaryLeavittClassicalK1` -- `K₁` in
  *classical* form: the stable group `colim_n GL_n(L)` modulo `E_∞(L)`, the
  subgroup generated by the elementary matrices of all finite ranks.
  `binaryLeavittElementaryColim_eq_top` says every stable class is elementary,
  and `binaryLeavittClassicalK1_subsingleton` proves the quotient trivial.
* `countable_of_finiteType` -- a finite-type algebra over a finite field is
  countable, which is what removes the countability hypothesis above.

## Internally closed dependency surface

The following load-bearing results are proved in Lean inside this repository;
none is represented by an axiom or theorem-shaped caller premise.

* `KunDecomposition.exists_expanderDecomposition` -- Kun's expander
  decomposition, Theorem 2.9, in the one-way full-sequence form used.
* `KunThomTheorem.isLEF_of_exactProductExpansion` -- the Kun--Thom centralizer
  obstruction, Theorem 2.10.
* `Shalom.exists_finitelyPresented_kazhdan_cover` -- Shalom's theorem: every
  finitely generated Kazhdan group is a quotient of a finitely presented one.
* `finiteFieldElementaryThree_hasKazhdanPropertyT` (in
  `PropertyT/FiniteFieldElementaryPropertyT`)
  -- property `(T)` at rank three, Theorem 5.7, for finite-type algebras over
  every finite field, with the explicit Kazhdan pair of
  `FreeElementaryPropertyT`.  This is the case the paper states and consumes;
  `LeavittRankEquivalence.rankSuccEquiv` spreads it to every rank.  The library
  consumes only this proved finite-field statement.

The non-LEF witness is likewise internal: no simplicity or finite-presentation
theorem for Thompson's `V` is used (`ThompsonFObstruction`,
`ThompsonWitness`).

## The `K₁` chain

Elementary and unconditional, replacing the localization-sequence input.
Appendix A of the manuscript is this chain written out.

* `BinaryLeavitt.K1_trivial` -- `K₁(L_k(1,2)) = 0` in Whitehead form.
* `BinaryLeavitt.exists_elementaryCertificate` -- that statement with its
  witness in hand: `diag(u,1)` as an explicit list of elementary matrices.
* `BinaryLeavitt.exists_moveList` -- the corner insertion `κ_[0](u)` of every
  unit as an explicit word of cylinder unipotents at the two atoms.
* `BinaryLeavitt.narrowReduction_holds` -- the two-exit elimination behind it.
* `BinaryLeavitt.glTwo_eq_elementary_holds`,
  `BinaryLeavitt.glFour_eq_elementary_holds` -- `GL = EL` at ranks two and four.

## What the definitions mean

An audit of axioms says nothing about whether the statement proved is the
statement intended.  These two discharge the definitional questions that carry
the most weight, as theorems rather than as caveats.

* `hasKazhdanPropertyT_iff_textbook` -- the real-orthogonal, own-universe
  property `(T)` used throughout is the textbook complex-unitary property
  quantified over every universe.
* `isLEF_iff_textbook` -- likewise for local embeddability.

## Trust surface

`GroupApproximation.Audit` prints the axiom report for these on an ordinary
build.  `scripts/Audit.lean` independently walks the transitive axiom closure
of the whole namespace and fails on anything beyond `propext`,
`Classical.choice`, and `Quot.sound`.
-/

namespace GroupApproximation.Public

open GroupApproximation

/-! ### Finite-radius marked-group neighborhoods -/

export GroupApproximation.MarkedGroupSpace
  (reducedWordLength wordBall mem_wordBall_iff exists_subset_wordBall
    cylinder_wordBall_subset_cylinder
    exists_wordBall_cylinder_subset_compl_operatorMFLocus
    isClosed_operatorMFLocus isOperatorMF_of_tendsto)

/-! ### The headline -/

export GroupApproximation (nonsofic_groups_exist countable_nonsofic_groups_exist
  countable_group_without_essentiallyFreeNearAction_exists
  universalLeavittEL4_not_admitsEssentiallyFreeNearAction
  isSofic_iff_admitsEssentiallyFreeNearAction
  universalLeavittEL4_not_isSofic
  ambient_full_profile exists_finitelyPresented_nonsofic_group
  exists_infinite_finitelyPresented_nonsofic_ambient_cover)

/-! ### The operator-norm MF obstruction -/

export GroupApproximation.ChosenNonMFTheorem
  (mark_normMFInvisible chosenFinitelyPresented_not_isWeakMF
    chosenFinitelyPresented_not_isOperatorMF
    countableWitness_not_isWeakMF exists_countable_not_isWeakMF
    exists_finitelyPresented_not_isWeakMF
    countableWitness_not_isOperatorMF exists_finitelyPresented_not_isOperatorMF
    not_every_group_isOperatorMF not_every_finitelyPresented_group_isOperatorMF)
export GroupApproximation.KazhdanCompressionCore
  (finiteNormal_le_normMFResidual not_isWeakMF_of_finiteNormal_le_defect
    finiteNormal_le_normMatrixCoronaKernel
    not_isOperatorMF_of_finiteNormal_le_defect)
export GroupApproximation
  (isOperatorMF_iff_normMFResidual_eq_bot
    isOperatorMFIncreasing_iff
    normMFQuotient_isOperatorMF
    exists_normMatrixCoronaRepresentation_ker_eq_normMFResidual
    existsUnique_normMFQuotient_factorization_to_isOperatorMF
    coronaMFResidual_eq_normMFResidual
    isOperatorMF_iff_coronaMFResidual_eq_bot
    coronaMFQuotient_isOperatorMF
    exists_normMatrixCoronaRepresentation_ker_eq_coronaMFResidual
    existsUnique_coronaMFQuotient_factorization_to_isOperatorMF
    isOperatorMF_of_residuallyFinite)
export GroupApproximation.IsOperatorMF (comap subgroup)
export GroupApproximation.OperatorMFQuotientNonclosure
  (operatorMF_not_closed_under_this_quotient)
export GroupApproximation.LiteralOperatorMFQuotientControls
  (source_isOperatorMF quotientMap_surjective)
export GroupApproximation
  (not_isOperatorMF_coprod_left not_isOperatorMF_coprod_right
    coprod_isFinitelyPresented)
export GroupApproximation
  (not_injective_of_coronaMFInvisible
    not_injective_of_coronaMFInvisible_of_target_embeds
    not_injective_to_isOperatorMF
    existsUnique_quotient_factorization_to_normMatrixCorona
    coronaMFResidual_eq_of_le_and_quotient_isOperatorMF)
export GroupApproximation.KazhdanCompressionCore
  (finiteNormal_uniform_invisibility
    not_isWeakMF_of_normalKazhdan_le_defect
    defectNormal_le_orbitDefectNormal
    orbitDefectNormal_le_compressionCentralizerDefect)
export GroupApproximation.MarkedCompressionInclusionData
  (not_isWeakMF_of_mem_finiteNormal not_isOperatorMF_of_mem_finiteNormal)
export GroupApproximation.KazhdanCompressionCore
  (finiteNormal_le_kernel_of_target_embeds)

/-! ### The literal eight-generator boundary -/

export GroupApproximation.LiteralNonMFPresentation
  (generator_card literal_algebraic_package)
export GroupApproximation.LiteralNonMFLinearWitness
  (literal_mark_ne_one literal_finitelyPresented_nontrivial_mark)
export GroupApproximation.LiteralFiniteDimensionalObstruction
  (literal_finiteDimensional_rep_not_injective)
export GroupApproximation.LiteralUniversalHorn
  (literalMarkedGroup_not_satisfies_literalQuasiIdentity)
export GroupApproximation.LiteralPresentationRadius
  (markedWord_length_le relator_wordLength_le_34
    relators_or_markedWord_length_le_34)
export GroupApproximation.LiteralMarkedCylinder
  (literalCylinder_nonempty literalCylinder_isClopen
    cylinder_relator_eq_one cylinder_markedWord_ne_one)
export GroupApproximation.CliffordAlgebraLamp
  (cliffordLamp_group_package cliffordLamp_permutation_package)
export GroupApproximation.ExplicitLinearModel (doubling_linear_model_package)
export GroupApproximation.AffineSL3Doubling (doubling_package)
export GroupApproximation.LiteralCyclicCalibration
  (mark_ne_one mark_central quotientMap_mark_val quotientMap_mark_ne_one
    quotientMap_mark_sq quotientMap_mark_central finiteDimensional_kill
    realizedQuotient_finiteDimensional_kill
    realizedQuotient_isOperatorMF
    exists_coronaRepresentation_mark_ne_one)
export GroupApproximation.CStarRecognitionConsequences
  (reducedCStarMF_recognition_undecidable
    maximalCStarMF_recognition_undecidable
    maximalCStar_finite_recognition_undecidable
    maximalCStar_stablyFinite_recognition_undecidable
    maximalCStar_directlyFinite_recognition_undecidable
    all_groupCStar_recognition_undecidable
    all_groupCStar_negative_sides_not_re)
export GroupApproximation.FixedSpaceStabilizer
  (compressionGroup_le_stabilizer compressionGroup_map_mem)
export GroupApproximation
  (map_marked_commutator_eq_one map_marked_commutator_eq_one_units
    compressionCentralizerDefect_le_ker
    commutator_conjugate_eq_commutator_sq_of_sq_eq_one)

/-! ### Conditional computability interface and algebraic consequences -/

export GroupApproximation.MarkovMFConsequences
  (MarkovWitness FinitePresentationSemantics operatorMFProperty
    AdianRabinReduction recognition_undecidable negative_side_not_re
    operatorMF_recognition_undecidable operatorMF_negative_side_not_re
    operatorMF_subgroup_hereditary exists_finitelyPresented_nonOperatorMF)
export GroupApproximation.OperatorMFMarkovWitness
  (positive_punit chosen_forbidden_subgroup
    exists_finitelyPresented_forbidden_subgroup)
export GroupApproximation (isOperatorMF_of_finite_standard
  not_isOperatorMF_of_subgroup)
export GroupApproximation.ProperProjectionCompression
  (star_isometry_mul_eq_one_and_reverse_ne exists_one_sided_inverse
    exists_leftInvertible_not_isUnit not_isDedekindFiniteMonoid
    not_isStablyFiniteRing no_injective_monoidHom_to_dedekindFinite
    no_faithfulTracialState)
export GroupApproximation.MarkedGroupSpace
  (mem_nhds_iff_exists_cylinder_subset tendsto_iff_eventually_relation
    tendsto_iff_eventually_cylinder)
export GroupApproximation
  (l2_opNorm_kronecker_le exists_pow_re_lt_half
    exists_opTensorPow_norm_sub_one_gt_one_of_diagonal_gap)
export GroupApproximation
  (IsOperatorMF.of_coprod_left IsOperatorMF.of_coprod_right
    not_isOperatorMF_coprod_left not_isOperatorMF_coprod_right
    coprod_isFinitelyPresented)

/-! ### Reach of the construction -/

export GroupApproximation (universalLeavitt_profile binaryLeavitt_finiteField_profile
  binaryLeavittUnits_not_isSofic binaryLeavittGL_not_isSofic
  universalLeavittEL3_not_isSofic)

/-! ### One endpoint per printed theorem -/

export GroupApproximation.Manuscript (ManuscriptProfile theoremA_exact theoremB_exact
  theoremB_Theta theoremB_Theta_apply theoremC_first
  theoremC_second theoremC_exact theoremC_covers_theoremB_groups
  theoremD_subgroups cor_fgring_printed cor_fgring_exact
  cor_fgring_countableFree)

/-! ### `K₁` as a group, and the countability that `cor:fgring` no longer needs -/

export GroupApproximation (binaryLeavittStableUnits_eq_top
  BinaryLeavittWhiteheadK1 binaryLeavittWhiteheadK1_subsingleton
  ClassicalGLColim elementaryColim BinaryLeavittClassicalK1
  binaryLeavittElementaryColim_eq_top binaryLeavittClassicalK1_subsingleton
  countable_of_finiteType)

/-! ### Internally proved load-bearing theorems -/

export GroupApproximation.KunDecomposition (exists_expanderDecomposition)
export GroupApproximation.KunThomTheorem (isLEF_of_exactProductExpansion)
export GroupApproximation.KazhdanFiniteGeneration
  (exists_symmetric_generating_finset fg_of_hasKazhdanPropertyT)
export GroupApproximation.Shalom (exists_finitelyPresented_kazhdan_cover)
export GroupApproximation (finiteFieldElementaryThree_hasKazhdanPropertyT)
export GroupApproximation (exists_kazhdan_finitelyPresented_cover_of_not_isSofic)

/-! ### The `K₁` chain -/

export GroupApproximation.BinaryLeavitt (K1_trivial narrowReduction_holds
  exists_elementaryCertificate exists_moveList
  glTwo_eq_elementary_holds glFour_eq_elementary_holds)

/-! ### The definitions are the textbook ones -/

export GroupApproximation (hasKazhdanPropertyT_iff_textbook isLEF_iff_textbook)
export GroupApproximation
  (ambient_hasKazhdanPropertyTComplex universalLeavitt_profile_textbook)
export GroupApproximation.FixedSpaceStabilizer
  (stabilizer mem_stabilizer_iff compressionGroup_le_stabilizer
    compressionGroup_map_mem)

end GroupApproximation.Public
