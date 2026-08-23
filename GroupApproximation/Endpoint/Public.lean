import GroupApproximation.Endpoint.MainResults
import GroupApproximation.Endpoint.NonMFImpact
import GroupApproximation.Endpoint.ManuscriptStatements
import GroupApproximation.Endpoint.SimultaneousStability
import GroupApproximation.Sofic.ChosenNonMFTheorem
import GroupApproximation.Sofic.FiniteNormalCompressionObstruction
import GroupApproximation.Sofic.NormMFUniversalCorona
import GroupApproximation.Sofic.NormMFCoronaRadical
import GroupApproximation.Sofic.FiniteNormalCoronaObstruction
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Sofic.MFRepresentationVariants
import GroupApproximation.Sofic.OperatorMFPositiveControls
import GroupApproximation.Sofic.OperatorMFIncreasingDimensions
import GroupApproximation.Sofic.MarkedMFClosed
import GroupApproximation.Sofic.OperatorMFQuotientNonclosure
import GroupApproximation.Sofic.NormMFPrintedConsequences
import GroupApproximation.Sofic.NormMFResidualExactQuotient
import GroupApproximation.Analysis.FaithfulTracialMatrix
import GroupApproximation.Analysis.ProperIsometryFromCompression
import GroupApproximation.Computability.MarkovMFConsequences
import GroupApproximation.Criterion.CompressionCentralizerDefect
import GroupApproximation.Criterion.FiniteDimensionalKill
import GroupApproximation.Monsters.CliffordAlgebraLamp
import GroupApproximation.Monsters.ExplicitLinearModel
import GroupApproximation.Sofic.CompressionDefectSquare
import GroupApproximation.Sofic.IntrinsicCompressionDefect
import GroupApproximation.Sofic.KazhdanAsymptoticCommutant
import GroupApproximation.Sofic.KazhdanSignCriterion
import GroupApproximation.Sofic.IntrinsicCompressionMFRadical
import GroupApproximation.Sofic.ManuscriptKazhdanTransport
import GroupApproximation.Sofic.LiteralFiniteDimensionalObstruction
import GroupApproximation.Monsters.UniversalMFEventHorizon
import GroupApproximation.Monsters.UniversalFinitelyPresentedTorsionFreeGroup
import GroupApproximation.Monsters.TorsionFreeConjugacyExtension
import GroupApproximation.Monsters.HitchhikerPayload
import GroupApproximation.Sofic.LiteralNonMFLinearWitness
import GroupApproximation.Sofic.LiteralNonMFPresentation
import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.LiteralSignFreeQuotient
import GroupApproximation.Sofic.KazhdanCliffordConstruction
import GroupApproximation.Sofic.ManuscriptExactWrappers
import GroupApproximation.Sofic.ManuscriptClosedWrappers
import GroupApproximation.Sofic.LiteralMFQuotientControls
import GroupApproximation.Sofic.LiteralNonMFConsequences
import GroupApproximation.Sofic.LiteralBaseTranslationLattice
import GroupApproximation.Sofic.LiteralBaseP13Replay
import GroupApproximation.Sofic.NormalKazhdanCompressionObstruction
import GroupApproximation.Sofic.NormalKazhdanHyperlinearKilled
import GroupApproximation.Sofic.NormalKazhdanMFRadical
import GroupApproximation.Sofic.QuestionTwoReduction
import GroupApproximation.Covers.KazhdanCover
import GroupApproximation.Kazhdan.ShalomFinitePresentation
import GroupApproximation.Kun.KunDecomposition
import GroupApproximation.KunThom.KunThomTheorem
import GroupApproximation.KOne.RefineLoopDischarge
import GroupApproximation.KOne.ClassicalKOne
import GroupApproximation.KOne.FactorizationCertificate
import GroupApproximation.Kazhdan.KazhdanTextbook
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration

/-!
# The public results

The library is organized by the order the mathematics was discovered, which is
not the order anyone should read it in.  This module is the reading path: the
declarations a referee actually needs, each named against the theorem it
establishes, and nothing else.  Follow the imports downward from here.

Nothing is proved in this module.  It re-exports, so that `#check` on any name
below lands on the real statement and its module.

`notes/CLAIM_MAP.md` is a generated statement-by-statement correspondence, read
out of margin notes; `non_mf_groups_exist.tex` is the manuscript for the non-MF
results below, and `scripts/check_non_mf_refs.py` is its counterpart gate.
This module is the short list.

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

## The simultaneous stability consequence

* `simultaneousStabilitySeed_not_isMixedApproximable` -- the direct product of
  the explicit nonsofic and non-operator-MF witnesses is outside the union of
  the Hamming and operator-norm approximation classes.
* `HasNoNontrivialMixedQuotient.isPointwisePStable` and
  `HasNoNontrivialMixedQuotient.isPointwiseOperatorNormStable` -- the two
  stability implications, proved internally through Hamming ultraproducts and
  the cofinite norm-matrix corona.  No conditional existence endpoint is
  exported for the unformalized Fournier--Facio construction.

## The operator-norm MF obstruction

* `ChosenNonMFTheorem.mark_normMFInvisible` -- the nontrivial marked word in
  the noncomputably chosen Shalom-cover witness is
  killed by every homomorphism to every norm-matrix ultraproduct.
* `ChosenMarkedPresentation.chosenFinitelyPresented_markedPackage` and
  `ChosenNonMFEndpoint.chosenFinitelyPresented_inclusionPackage` -- the exact
  algebraic packages carried by that chosen witness; these names deliberately
  do not identify it with the paper's separate literal presentation.
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
* `KazhdanCompressionCore.finiteNormal_le_coronaMFResidual` -- the same
  finite-normal criterion stated as containment in the intersection of all
  cofinite norm-matrix-corona kernels.
* `KazhdanCompressionCore.not_isOperatorMF_of_finiteNormal_le_defect` -- the
  same criterion as a direct obstruction to the standard cofinite-corona
  definition of operator MF.
* `KazhdanCompressionCore.defectSquare_centralInvolution_mem_normMatrixCStarCoronaKernel`
  and `not_isOperatorMF_of_defectSquare_eq_centralInvolution` -- the
  reader-facing one-sign specialization: if the square of one compression
  defect is a nontrivial central involution, every genuine corona model kills
  it and the ambient group is not operator MF.
* `KazhdanAsymptoticCommutant.manuscriptKazhdanTransport` -- the all-elements,
  all-compressors transport theorem: a uniformly bounded asymptotic commutant
  is preserved in both directions by the subgroup generated by one-sided
  compressors.
* `KazhdanAsymptoticCommutant.manuscriptCompressionRadical` -- the intrinsic
  corollary: every finite normal subgroup inside the compression-centralizer
  defect lies in the norm-MF residual.
* `KazhdanCliffordConstruction.kazhdanCliffordConstruction` -- the unconditional
  abstract construction from a finitely presented Kazhdan group, a proper
  injective self-embedding, and one element outside its range; the resulting
  finitely presented group has a nontrivial Clifford sign killed by every
  norm-matrix-corona representation and is not operator MF.
* `isOperatorMF_iff_normMFResidual_eq_bot` and
  `normMFQuotient_isOperatorMF` -- the universal norm-MF quotient is itself
  operator MF, and residual triviality exactly characterizes operator MF for
  countable groups.
* `IsCDEOperatorMF` and `isCDEOperatorMF_iff_isOperatorMF` -- the literal
  Carrión--Dadarlat--Eckhardt definition (countable group, strictly increasing
  positive dimensions, and the unitary group of the actual C-star quotient)
  and its proved equivalence with the coordinate model used internally.
* `normMatrixCoronaUnitaryEquiv` -- the canonical polar-correction
  equivalence from the coordinate quotient of exact unitaries to the unitary
  group of the actual C-star quotient.
* `finiteNormal_le_normMatrixCStarCoronaKernel` and
  `normalKazhdan_le_normMatrixCStarCoronaKernel` -- the finite-normal and
  normal-Kazhdan obstructions with the manuscript's actual C-star target.
* `isOperatorMFIncreasing_iff` -- the arbitrary positive dimension sequences
  used by the internal coordinate model are equivalent to the strictly
  increasing convention.
* `ChosenNonMFTheorem.not_every_group_isOperatorMF` -- the direct negative
  answer to the universal operator-MF assertion.

## Three independently exposed non-MF mechanisms

* `LiteralNonMFEndpoint.literal_not_isOperatorMF` is the closed central-sign
  route: the nontrivial central Clifford involution is the square of a
  compression defect and every norm-matrix-corona homomorphism kills it.
* `LiteralSignFreeQuotient.signFreeQuotient_not_isOperatorMF` is the closed
  sign-free route: after quotienting out that central sign, a noncentral
  involutive compression witness still kills a surviving unsquared lamp
  commutator.  `exists_finitelyPresented_signFree_not_isOperatorMF` is its
  premise-free finitely presented existence endpoint.
* `QuestionTwoReduction.not_isOperatorMF_of_nontrivial_normal_kazhdan_defect`
  is the normal-Kazhdan route: a nontrivial normal property-`(T)` subgroup in
  the compression defect is killed elementwise and obstructs operator MF.
  `normalKazhdan_le_normMFResidual_of_hyperlinear_killed` records the stronger
  detector against an arbitrary tracial-shadow kill theorem.  These analytic
  implications are complete; constructing the torsion-free routed input by
  Hull small cancellation remains outside Lean's current group-theory library.

## Marked-limit stability of operator MF

* `OperatorNormAmplification.exists_tensorPower_pair_far` -- bounded tensor
  powers amplify any positive unitary-pair gap beyond the universal threshold
  one, with dimension-free error control.
* `OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one` --
  for countable groups, operator MF is equivalent to local norm approximation
  with separation constant exactly one.
* `MarkedGroupSpace.isClosed_operatorMFLocus` and
  `MarkedGroupSpace.isOpen_compl_operatorMFLocus` -- operator-MF marked groups
  form a closed locus, equivalently non-MF is open, in every fixed rank.
* `MarkedGroupSpace.exists_wordBall_cylinder_subset_compl_operatorMFLocus` --
  every non-MF marked group has a finite-radius Cayley-ball certificate.
* `MarkedGroupSpace.isOperatorMF_of_tendsto` -- the arbitrary-filter marked
  limit theorem, of which sequential closure is an immediate instance.

## The literal eight-generator theorem

The paper's displayed group is now the unconditional formal witness.  Its
proof is exposed in the same conceptual order as the manuscript: the exact
P13 property-`(T)` certificate, `w = u²`, Kazhdan pinning, finite-normal
annihilation, and Clifford detection.

* `LiteralNonMFPresentation.manuscriptLiteralPresentation` and
  `LiteralNonMFLinearWitness.literal_mark_ne_one` -- the exact displayed
  finite presentation, its relations, and a genuine nontrivial marked
  involution.
* `LiteralNonMFEndpoint.manuscriptTheoremA` -- the hypothesis-free printed
  theorem, including the corona kernel statement and the group and C-star
  non-MF conclusions.
* `LiteralNonMFEndpoint.negativeCorner_kazhdanTransport_contradiction` -- the
  short reader-facing proof: cut a separated central sign to its negative
  corner, then contradict `w = u² → 1` from Kazhdan transport.
* `KazhdanCliffordConstruction.negativeCorner_kazhdanTransport_contradiction`
  -- the same short proof for the reusable construction from any finitely
  presented Kazhdan group with a proper injective self-embedding.
* `LiteralNonMFEndpoint.manuscriptTheoremD` -- the hypothesis-free reduced
  group C-star endpoint: separable, faithfully tracial, stably finite in every
  finite matrix amplification, and non-MF.
* `KazhdanCompressionCore.manuscriptCentralSignCriterion` -- the exact
  reader-facing abstraction of the five-line proof: one compression defect
  whose square is a nontrivial central involution is killed in every genuine
  norm-matrix C-star corona and obstructs operator MF.
* `LiteralP13HodgeCertificate.cleanP13Certificate` and `p13_hodge_gap` -- the
  deliberately weakened public certificate: the exact residual arithmetic is
  hidden behind the human constants `1/250` and `1/500`, yielding the clean
  represented Hodge estimate `Delta₁ ≥ (1/500)I`.
* `LiteralBaseP13Replay.yFromUZXY_eq` and `closure_Z_XY_eq_top` -- an exact
  finite-relator replay proving that the abstract rotation presentation is
  generated by `Z` and `X * Y`.
* `LiteralFiniteDimensionalObstruction.literal_finiteDimensional_rep_not_injective`
  -- every finite-dimensional linear representation of the literal group is
  nonfaithful.

## Closed impact endpoints

`NonMFImpact` collects only premise-free conclusions, and this section
re-exports the closed endpoints from their home modules alongside it: the
six-generator bound, the nonempty clopen non-MF cylinder, the locally
finite MF lamp kernel and MF vertical quotient inside the finitely
generated non-MF witness, the sofic and hyperlinear witness separations,
the residually finite/sofic/MF affine base, the entire scaling family,
the cyclic exact-model obstruction, quotient nonclosure, the uniform
finite obstruction, and the torsion-free limitation of finite-normal
methods.  None accepts a property-`(T)`, approximation, permanence, or
literature premise from a caller.

## Consequences and reusable obstruction APIs

* `not_injective_of_coronaMFInvisible`,
  `KazhdanCompressionCore.finiteNormal_uniform_invisibility`, and its
  positive-model formulation
  `KazhdanCompressionCore.finiteNormal_uniform_invisibility_positiveModel` --
  portability and uniform killing of the obstruction.
* `existsUnique_quotient_factorization_to_normMatrixCorona` -- exact quotient
  factorization in the cofinite-corona language.
* `MarkovMFConsequences.operatorMF_recognition_undecidable` -- the computability
  reduction at the recursive presentation coding, generic in the source problem
  and conditional on an explicitly supplied computable Adian--Rabin
  transformation and its correctness proof; no such external transformation is
  postulated by the library.  `MarkovMFConsequences.recognition_undecidable` is
  the same pullback with the coding left open.
* `ProperProjectionCompression` -- the one-sided compression API, including
  an explicit left-invertible nonunit, failure of direct and stable finiteness,
  and obstruction to a faithful tracial state.

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
  (cylinder isClopen_cylinder tendsto_iff_eventually_relation
    tendsto_iff_eventually_cylinder
    reducedWordLength wordBall mem_wordBall_iff exists_subset_wordBall
    cylinder_wordBall_subset_cylinder operatorMFLocus
    exists_cylinder_subset_compl_operatorMFLocus
    exists_wordBall_cylinder_subset_compl_operatorMFLocus
    isClosed_operatorMFLocus isOpen_compl_operatorMFLocus
    isOperatorMF_of_tendsto)
export GroupApproximation.OperatorNormAmplification
  (exists_tensorPower_pair_far)
export GroupApproximation.OperatorMFLocalNormalization
  (isNormApproximable_one isOperatorMF_iff_isNormApproximable_one)

/-! ### The headline -/

export GroupApproximation (nonsofic_groups_exist countable_nonsofic_groups_exist
  countable_group_without_essentiallyFreeNearAction_exists
  universalLeavittEL4_not_admitsEssentiallyFreeNearAction
  isSofic_iff_admitsEssentiallyFreeNearAction
  universalLeavittEL4_not_isSofic
  ambient_full_profile exists_finitelyPresented_nonsofic_group
  exists_infinite_finitelyPresented_nonsofic_ambient_cover)

/-! ### Simultaneous Hamming/operator-norm stability -/

export GroupApproximation
  (IsMixedApproximable HasNoNontrivialMixedQuotient
    HasNoNontrivialSoficQuotient HasNoNontrivialOperatorMFQuotient
    HasNoNontrivialFiniteQuotient HammingAlmostRepresentation
    IsPointwisePStable IsPointwiseOperatorNormStable
    not_isMixedApproximable_prod
    simultaneousStabilitySeed_not_isMixedApproximable)

/-! ### The operator-norm MF obstruction -/

export GroupApproximation.ChosenNonMFTheorem
  (mark_normMFInvisible chosenFinitelyPresented_not_isWeakMF
    chosenFinitelyPresented_not_isOperatorMF
    countableWitness_not_isWeakMF exists_countable_not_isWeakMF
    exists_finitelyPresented_not_isWeakMF
    countableWitness_not_isOperatorMF exists_finitelyPresented_not_isOperatorMF
    exists_countable_finitelyPresented_not_isOperatorMF
    not_every_countable_group_isOperatorMF
    not_every_group_isOperatorMF not_every_finitelyPresented_group_isOperatorMF)
export GroupApproximation.ChosenMarkedPresentation
  (chosenFinitelyPresented_markedPackage)
export GroupApproximation.ChosenNonMFEndpoint
  (chosenFinitelyPresented_inclusionPackage)
export GroupApproximation.Monsters
  (UniversalFinitelyPresentedGroup UniversalMFEventHorizon
    TorsionFreePresentationCode
    UniversalFinitelyPresentedTorsionFreeGroup
    UniversalCentralizerPayload
    HitchhikerPayload
    TorsionFreeConjugacyExtension
    embeds_universalFinitelyPresentedGroup
    exists_mulEquiv_codedPresentedGroup
    embeds_universalFinitelyPresentedGroup_of_finite
    embeds_universalFinitelyPresentedTorsionFreeGroup
    universalCentralizerElement universalCentralizerElement_ne_one
    universalCentralizerElement_mem_center
    embeds_universalCentralizerPayload
    embeds_freeGroup_universalCentralizerPayload
    universalCentralizerPayload_containsEveryFiniteRankFreeGroup
    universalCentralizerPayload_package
    every_finitelyPresented_torsionFree_group_embeds_centralizer
    torsionFreeConjugacyEmbedding
    torsionFreeConjugacyEmbedding_injective
    torsionFreeConjugacyEmbedding_isConj
    freeTwoToHitchhikerPayload
    freeTwoToHitchhikerPayload_injective
    universalCentralizerPayloadToHitchhikerPayload
    universalCentralizerPayloadToHitchhikerPayload_injective
    hitchhikerCentralizerElement hitchhikerCentralizerElement_ne_one
    hitchhikerCentralizerElement_mem_center
    embeds_hitchhikerPayload
    hitchhikerPayload_containsEveryFiniteRankFreeGroup
    hitchhikerPayload_package
    eventHorizonMark eventHorizonMark_ne_one
    eventHorizonMark_normMFInvisible
    eventHorizonMark_coronaMFInvisible
    map_eventHorizonMark_eq_one_to_isOperatorMF
    no_injective_map_to_isOperatorMF
    universalMFEventHorizon_not_isOperatorMF
    map_eventHorizonMark_eq_one_to_finite
    no_injective_map_to_finite
    universalMFEventHorizon_not_isSofic
    universalMFEventHorizon_package
    every_finite_group_enters_no_faithful_finite_map_leaves)
export GroupApproximation.Monsters
  (ContainsEveryFiniteRankFreeGroup lift_conj
    isVerballyComplete_of_twoConjugacyClasses)
export GroupApproximation.Monsters.IsVerballyComplete
  (exists_conj_pow_eq exists_commutatorElement_conj_eq)
export GroupApproximation.KazhdanCompressionCore
  (finiteNormal_le_normMFResidual finiteNormal_le_normMFResidual_of_hyperlinear_killed
    not_isWeakMF_of_finiteNormal_le_defect
    centralInvolution_mem_normMatrixCStarCoronaKernel
    defectSquare_centralInvolution_mem_normMatrixCStarCoronaKernel
    not_isOperatorMF_of_centralInvolution_mem_defect
    not_isOperatorMF_of_defectSquare_eq_centralInvolution
    manuscriptCentralSignCriterion
    finiteNormal_le_coronaMFResidual
    finiteNormal_le_normMatrixCoronaKernel
    finiteNormal_le_normMatrixCStarCoronaKernel
    not_isOperatorMF_of_finiteNormal_le_defect)
export GroupApproximation.QuestionTwoReduction
  (not_isOperatorMF_of_nontrivial_normal_kazhdan_defect)
export GroupApproximation.KazhdanAsymptoticCommutant
  (manuscriptKazhdanTransport manuscriptCompressionRadical)
export GroupApproximation.KazhdanCliffordConstruction
  (every_cstar_corona_hom_kills_mark kazhdanCliffordConstruction)
export GroupApproximation.LiteralP13HodgeCertificate
  (cleanP13Certificate p13_hodge_gap
    p13_generatorLaplacian_quadratic_gap p13_hasKazhdanPropertyT)
export GroupApproximation
  (IsCDEOperatorMF isCDEOperatorMF_iff_isOperatorMF
    IsPurelyMatricialField IsPurelyPermutationField IsTracePMF IsPFF IsPPF
    FailsEveryStandardMFConvention
    not_of_implies_isOperatorMF
    failsEveryStandardMFConvention_of_not_isOperatorMF
    normMatrixCoronaUnitaryEquiv
    unitaryCoronaToCStarCoronaUnitary
    unitaryCoronaToCStarCoronaUnitary_injective
    unitaryCoronaToCStarCoronaUnitary_surjective
    isOperatorMF_iff_normMFResidual_eq_bot
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
export GroupApproximation.IsPurelyPermutationField (isOperatorMF)
export GroupApproximation.IsOperatorMF (comap subgroup)
export GroupApproximation.OperatorMFQuotientNonclosure
  (operatorMF_not_closed_under_this_quotient)
export GroupApproximation
  (not_injective_of_coronaMFInvisible
    not_injective_of_coronaMFInvisible_of_target_embeds
    not_injective_to_isOperatorMF
    existsUnique_quotient_factorization_to_normMatrixCorona
    coronaMFResidual_eq_of_le_and_quotient_isOperatorMF)
export GroupApproximation.KazhdanCompressionCore
  (finiteNormal_uniform_invisibility
    finiteNormal_uniform_invisibility_positiveModel
    not_isWeakMF_of_normalKazhdan_le_defect
    normalKazhdan_le_normMFResidual normalKazhdan_le_coronaMFResidual
    normalKazhdan_le_normMatrixCStarCoronaKernel
    normalKazhdanDefectPart_le_normMFResidual
    existsUnique_defectNormal_factorization_to_normMatrixCStarCorona
    normalKazhdan_le_normMFResidual_of_hyperlinear_killed
    normalKazhdan_le_normMatrixCStarCoronaKernel_of_hyperlinear_killed
    defectNormal_le_orbitDefectNormal
    orbitDefectNormal_le_compressionCentralizerDefect)
export GroupApproximation.KazhdanAsymptoticCommutant
  (transport transport_star transport_both
    compressionGroup_le_asymptoticCommutantStabilizer
    compressionGroup_transport_both
    compressionCentralizerDefect_eq_one_in_hyperlinearHom
    finiteNormal_le_normMFResidual_of_le_compressionCentralizerDefect)
export GroupApproximation.MarkedCompressionInclusionData
  (not_isOperatorMF_of_mem_finiteNormal)

/-! ### The literal eight-generator theorem -/

export GroupApproximation.LiteralNonMFPresentation
  (literalEightGeneratorPresentation manuscriptLiteralPresentation)
export GroupApproximation.LiteralNonMFLinearWitness (literal_mark_ne_one)
export GroupApproximation.LiteralNonMFEndpoint
  (inclusionData compressionRoot compressionDefect
    mark_eq_compressionDefect_sq
    compressionDefect_sq_ne_one kazhdanPinning
    negativeCorner_kazhdanTransport_contradiction
    literalInvolutionSubgroup_le_defectNormal
    literalInvolutionSubgroup_le_normMatrixCStarCoronaKernel
    literalInvolutionSubgroup_le_normMatrixCoronaKernel
    literal_mark_eq_one_in_normMatrixCStarCorona
    literal_mark_eq_one_in_CStarCorona
    literal_mark_eq_one_in_unitaryCorona
    literal_mark_mem_manuscriptCoronaMFResidual
    literal_mark_normMFInvisible
    cliffordSign_blackHole literal_not_isOperatorMF
    literal_not_isCDEOperatorMF
    literal_not_of_implies_isOperatorMF
    literal_failsEveryStandardMFConvention
    literal_maximalGroupCStar_not_hasMFEmbedding
    literal_maximalGroupCStar_not_isMFAlgebra
    literal_reducedGroupCStar_not_hasMFEmbedding
    literal_reducedGroupCStar_not_isMFAlgebra
    manuscriptTheoremA manuscriptTheoremD)
export GroupApproximation.LiteralSignFreeQuotient
  (signFree_collapse signFreeQuotient_finitelyPresented
    signFreeQuotient_not_isCDEOperatorMF signFreeQuotient_not_isOperatorMF
    exists_finitelyPresented_signFree_not_isOperatorMF)
export GroupApproximation.LiteralBaseTranslationLattice
  (latticeToBase_injective latticeToBase_range latticeEquivTranslations)
export GroupApproximation.LiteralBaseP13Replay
  (yFromUZXY_eq closure_Z_XY_eq_top)
export GroupApproximation.LiteralFiniteDimensionalObstruction
  (literal_finiteDimensional_rep_not_injective)
export GroupApproximation.NonMFImpact
  (witness_hyperlinear_nonMF
    witness_sofic_hyperlinear_nonMF
    witness_reducedGroupCStar_stablyFinite_nonMF
    affineBase_residuallyFinite_sofic_MF
    scalingFamily_finitelyPresented_nonMF
    cyclicBase_exactModel_obstruction
    finiteNormal_obstruction_is_trivial_in_torsionFree_groups
    sofic_nonMF_is_hyperlinear_nonMF)
export GroupApproximation.LiteralSixGenerator
  (literal_sixGenerated_finitelyPresented_nonMF)
export GroupApproximation.LiteralMarkedCylinder
  (literal_nonempty_clopen_nonMF_cylinder)
export GroupApproximation.LiteralWitnessConsequences
  (literalWitness_locallyFiniteKernel_nonMF literalWitness_sofic_nonMF)
export GroupApproximation.OperatorMFQuotientNonclosure
  (operatorMF_not_closed_under_this_quotient)
export GroupApproximation.LiteralUniformObstruction
  (literal_uniform_operatorNorm_obstruction)
export GroupApproximation.CliffordAlgebraLamp
  (cliffordLamp_group_package cliffordLamp_permutation_package)
export GroupApproximation.ExplicitLinearModel (doubling_linear_model_package)
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
export GroupApproximation (isOperatorMF_of_finite_standard
  not_isOperatorMF_of_subgroup)
export GroupApproximation.ProperProjectionCompression
  (star_isometry_mul_eq_one_and_reverse_ne exists_one_sided_inverse
    exists_leftInvertible_not_isUnit not_isDedekindFiniteMonoid
    not_isStablyFiniteRing no_injective_monoidHom_to_dedekindFinite
    no_faithfulTracialState)

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

end GroupApproximation.Public
