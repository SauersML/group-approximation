import GroupApproximation.Computability.BooneWordProblemUndecidable
import GroupApproximation.Computability.MFRadicalComputer
import GroupApproximation.Computability.WordProblemRE
import GroupApproximation.Manuscript.NonMFNotes.Full.AbelianBoundary.Torsion
import GroupApproximation.Manuscript.NonMFNotes.Full.AdianRabin.Unconditional
import GroupApproximation.Manuscript.NonMFNotes.Full.Arithmetic.AdianRabinOutput
import GroupApproximation.Manuscript.NonMFNotes.Full.Arithmetic.MFArithmetic
import GroupApproximation.Manuscript.NonMFNotes.Full.Arithmetic.Undecidable
import GroupApproximation.Manuscript.NonMFNotes.Full.CliffordAmenable.RealizedQuotient
import GroupApproximation.Manuscript.NonMFNotes.Full.ExactResidual.Defects
import GroupApproximation.Manuscript.NonMFNotes.Full.ExactResidual.ExactResidual
import GroupApproximation.Manuscript.NonMFNotes.Full.Exactness.BlockCliffordPropertyA
import GroupApproximation.Manuscript.NonMFNotes.Full.Exactness.FreeProductPropertyA
import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessGHW.AmenablePropertyA
import GroupApproximation.Manuscript.NonMFNotes.Full.FFRealization.Presented
import GroupApproximation.Manuscript.NonMFNotes.Full.FFRealization.Realization
import GroupApproximation.Manuscript.NonMFNotes.Full.FixedRadicalMembership.Bridge
import GroupApproximation.Manuscript.NonMFNotes.Full.FixedRadicalMembership.Retraction
import GroupApproximation.Manuscript.NonMFNotes.Full.Gstar.A5Relation
import GroupApproximation.Manuscript.NonMFNotes.Full.Gstar.Approximation
import GroupApproximation.Manuscript.NonMFNotes.Full.Gstar.WreathStar
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.SolvableAmenable
import GroupApproximation.Manuscript.NonMFNotes.Full.LiteralCertificate.Classification
import GroupApproximation.Manuscript.NonMFNotes.Full.LiteralCertificate.Semantics
import GroupApproximation.Manuscript.NonMFNotes.Full.Prose.BlockComparison
import GroupApproximation.Manuscript.NonMFNotes.Full.Prose.DeligneType
import GroupApproximation.Manuscript.NonMFNotes.Full.Prose.E0Kernel
import GroupApproximation.Manuscript.NonMFNotes.Full.Prose.FiniteNormalRemark
import GroupApproximation.Manuscript.NonMFNotes.Full.RadicalArithmetic.Arithmetic
import GroupApproximation.Manuscript.NonMFNotes.Full.RadicalArithmetic.Semantics
import GroupApproximation.Manuscript.NonMFNotes.Full.TorsionFree.Configuration
import GroupApproximation.Manuscript.NonMFNotes.Full.VisibleQuotient.Basic
import GroupApproximation.Manuscript.NonMFNotes.Full.VisibleQuotient.Targets
import GroupApproximation.Manuscript.SpectralPaper.MainTheorems
import GroupApproximation.Monsters.LiteralBaseCompleteness
import GroupApproximation.Monsters.LiteralCyclicCalibration
import GroupApproximation.Sofic.BlockCliffordTowerSofic
import GroupApproximation.Sofic.ConjugationDatumAnyUniverse
import GroupApproximation.Sofic.DefectActionAnyUniverse
import GroupApproximation.Sofic.DefectRadicalAnyUniverse
import GroupApproximation.Sofic.FiniteNormalAnyUniverse
import GroupApproximation.Sofic.LiteralBaseP13PropertyTBridge
import GroupApproximation.Sofic.LiteralBlockNormalForm
import GroupApproximation.Sofic.LiteralFiniteDimensionalObstruction
import GroupApproximation.Sofic.LiteralMFQuotientControls
import GroupApproximation.Sofic.LiteralNonMFConsequences
import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.LiteralNonMFLinearWitness
import GroupApproximation.Sofic.LiteralNonMFPresentation
import GroupApproximation.Sofic.LiteralRelatorObstruction
import GroupApproximation.Sofic.LiteralSignFreeQuotient
import GroupApproximation.Sofic.LiteralSoficAssembly
import GroupApproximation.Sofic.LiteralUniversalHorn
import GroupApproximation.Sofic.LocallyFiniteMF
import GroupApproximation.Sofic.ManuscriptExactWrappers
import GroupApproximation.Sofic.ManuscriptSubgroupSpecializations
import GroupApproximation.Sofic.NormalKazhdanAnyUniverse
import GroupApproximation.Sofic.OperatorMFPositiveControls
import GroupApproximation.Sofic.ProjectionCompressionCollapse
import GroupApproximation.Sofic.RealizationFromUniversalGroup
import GroupApproximation.Sofic.ScalingFamilyEndpoint
import GroupApproximation.Sofic.TorsionSpectralCollapse
import GroupApproximation.Sofic.TraceSeparationEndpoint

/-!
# `non_mf_group_notes.tex`: the notes aggregator

This file imports the Lean endpoint of every numbered claim of
`non_mf_group_notes.tex` that has one on the main branch, together with the
`Full/*` modules of the notes swarm, and restates each one under a name keyed
to its printed label: `notes_<label>` for a numbered claim or remark, and
`notes_prose_<name>` for a badged prose paragraph.

Every entry is an `alias` of an already proved declaration.  This file adds no
mathematics and no hypotheses, so the aliases have the same statements and
the same axioms as their targets.

Status is recorded honestly in the docstrings.  An entry marked PARTIAL proves
less than the printed claim, and the docstring names the missing clause and
the lane that is working on it.  No clause is supplied as a hypothesis.

Every numbered claim has at least one entry.  Four are PARTIAL:
* `thm:fixed-radical-membership`: only the retraction clauses and the
  conditional shape;
* `thm:exact-mf-residual`: only the equivalence with
  `IsOperatorMF TerminalAmalgam`;
* `thm:notes-abelian-boundary`: only "MF implies torsion-free";
* `thm:torsionfree`: only the routed step.

The four data declarations of the manifest (`LiteralBlockNormalForm.markedGroupEquivModel`,
`LiteralBlockNormalForm.lampKernelEquiv`, `LiteralVerticalBridge.verticalEquiv`,
`LiteralSoficAssembly.lampEquiv`) and `LiteralBaseCompleteness.baseAffineEquiv`
are equivalences, not propositions.  They are reached through the imports and
are not re-aliased.
-/

namespace GroupApproximation.Full.NNRoot


/-! ## `def:E` (tex l.159) -/

/-- `def:E` (`non_mf_group_notes.tex` l.159): the literal presentation of `E`. Alias of
`GroupApproximation.LiteralNonMFPresentation.manuscriptLiteralPresentation`. -/
alias notes_def_E := GroupApproximation.LiteralNonMFPresentation.manuscriptLiteralPresentation


/-! ## `prop:literal-base-T` (tex l.194) -/

/-- `prop:literal-base-T` (`non_mf_group_notes.tex` l.194): the base has Kazhdan's property
(T). Alias of
`GroupApproximation.LiteralBaseP13PropertyTBridge.manuscriptBaseHasKazhdanPropertyT`. -/
alias notes_prop_literal_base_T := GroupApproximation.LiteralBaseP13PropertyTBridge.manuscriptBaseHasKazhdanPropertyT


/-! ## `rem:classical-base` (tex l.212) -/

/-- `rem:classical-base` (`non_mf_group_notes.tex` l.212): completeness of the twenty-relator
base presentation (the base is the affine group; the equivalence itself is the data
`LiteralBaseCompleteness.baseAffineEquiv`). Alias of
`GroupApproximation.LiteralBaseCompleteness.affineQuotient_injective`. -/
alias notes_rem_classical_base := GroupApproximation.LiteralBaseCompleteness.affineQuotient_injective


/-! ## `lem:linear` (tex l.222) -/

/-- `lem:linear` (`non_mf_group_notes.tex` l.222): the linear model. Alias of
`GroupApproximation.ManuscriptExactWrappers.manuscriptLinearModel`. -/
alias notes_lem_linear := GroupApproximation.ManuscriptExactWrappers.manuscriptLinearModel


/-! ## `prop:witness` (tex l.267) -/

/-- `prop:witness` (`non_mf_group_notes.tex` l.267): the mark is nontrivial. Alias of
`GroupApproximation.LiteralNonMFLinearWitness.literal_mark_ne_one`. -/
alias notes_prop_witness := GroupApproximation.LiteralNonMFLinearWitness.literal_mark_ne_one


/-! ## `cor:relator-uniform` (tex l.315) -/

/-- `cor:relator-uniform` (`non_mf_group_notes.tex` l.315): the relator-uniform obstruction.
Alias of
`GroupApproximation.LiteralRelatorObstruction.literal_relator_uniform_obstruction`. -/
alias notes_cor_relator_uniform := GroupApproximation.LiteralRelatorObstruction.literal_relator_uniform_obstruction


/-! ## `thm:signfree` (tex l.357) -/

/-- `thm:signfree` (`non_mf_group_notes.tex` l.357): sign-free collapse. Alias of
`GroupApproximation.LiteralSignFreeQuotient.signFree_collapse`. -/
alias notes_thm_signfree_collapse := GroupApproximation.LiteralSignFreeQuotient.signFree_collapse

/-- `thm:signfree` (`non_mf_group_notes.tex` l.357): the sign-free quotient is not MF. Alias
of `GroupApproximation.LiteralSignFreeQuotient.signFreeQuotient_not_isCDEOperatorMF`. -/
alias notes_thm_signfree_not_mf := GroupApproximation.LiteralSignFreeQuotient.signFreeQuotient_not_isCDEOperatorMF

/-- `thm:signfree` (`non_mf_group_notes.tex` l.357): the commutator is not a power of the
mark. Alias of `GroupApproximation.LiteralSignFreeQuotient.commutator_not_zpow_mark`. -/
alias notes_thm_signfree_commutator := GroupApproximation.LiteralSignFreeQuotient.commutator_not_zpow_mark


/-! ## `thm:reduced` (tex l.393) -/

/-- `thm:reduced` (`non_mf_group_notes.tex` l.393): the reduced group C*-algebra endpoint.
Alias of `GroupApproximation.LiteralNonMFEndpoint.manuscriptTheoremD`. -/
alias notes_thm_reduced := GroupApproximation.LiteralNonMFEndpoint.manuscriptTheoremD


/-! ## `thm:Esofic` (tex l.426) -/

/-- `thm:Esofic` (`non_mf_group_notes.tex` l.426): `E` is sofic. Alias of
`GroupApproximation.LiteralSoficAssembly.markedGroup_isSofic`. -/
alias notes_thm_Esofic := GroupApproximation.LiteralSoficAssembly.markedGroup_isSofic


/-! ## `lem:mftrace-group` (tex l.465) -/

/-- `lem:mftrace-group` (`non_mf_group_notes.tex` l.465): MF traces and groups. Alias of
`GroupApproximation.manuscriptMFTraceGroupBridge`. -/
alias notes_lem_mftrace_group := GroupApproximation.manuscriptMFTraceGroupBridge


/-! ## `thm:trace` (tex l.498) -/

/-- `thm:trace` (`non_mf_group_notes.tex` l.498): trace separation. Alias of
`GroupApproximation.manuscriptTraceSeparation`. -/
alias notes_thm_trace := GroupApproximation.manuscriptTraceSeparation


/-! ## `thm:transport-variants` (tex l.543) -/

/-- `thm:transport-variants` (`non_mf_group_notes.tex` l.543): weighted transport variants.
Alias of `GroupApproximation.ManuscriptExactWrappers.manuscriptWeightedTransportSubgroup`. -/
alias notes_thm_transport_variants := GroupApproximation.ManuscriptExactWrappers.manuscriptWeightedTransportSubgroup


/-! ## `def:pattern` (tex l.595) -/

/-- `def:pattern` (`non_mf_group_notes.tex` l.595): marked Kazhdan patterns. Alias of
`GroupApproximation.ManuscriptExactWrappers.manuscriptMarkedKazhdanPattern_anyUniverse`. -/
alias notes_def_pattern := GroupApproximation.ManuscriptExactWrappers.manuscriptMarkedKazhdanPattern_anyUniverse


/-! ## `def:invisible` (tex l.622) -/

/-- `def:invisible` (`non_mf_group_notes.tex` l.622): HS-invisible elements. Alias of
`GroupApproximation.ManuscriptExactWrappers.manuscriptHSInvisibleCharacterization`. -/
alias notes_def_invisible := GroupApproximation.ManuscriptExactWrappers.manuscriptHSInvisibleCharacterization


/-! ## `thm:criterion` (tex l.639) -/

/-- `thm:criterion` (`non_mf_group_notes.tex` l.639): the finite normal obstruction criterion.
Alias of
`GroupApproximation.ManuscriptExactWrappers.manuscriptFiniteNormalObstructionCriterion_anyUniverse`. -/
alias notes_thm_criterion := GroupApproximation.ManuscriptExactWrappers.manuscriptFiniteNormalObstructionCriterion_anyUniverse


/-! ## `cor:marked-obstruction` (tex l.715) -/

/-- `cor:marked-obstruction` (`non_mf_group_notes.tex` l.715): the mark lies in the MF
residual. Alias of
`GroupApproximation.LiteralNonMFEndpoint.literal_mark_mem_manuscriptCoronaMFResidual`. -/
alias notes_cor_marked_obstruction_residual := GroupApproximation.LiteralNonMFEndpoint.literal_mark_mem_manuscriptCoronaMFResidual

/-- `cor:marked-obstruction` (`non_mf_group_notes.tex` l.715): the mark is nontrivial. Alias
of `GroupApproximation.LiteralNonMFLinearWitness.literal_mark_ne_one`. -/
alias notes_cor_marked_obstruction_ne_one := GroupApproximation.LiteralNonMFLinearWitness.literal_mark_ne_one


/-! ## `cor:generaltransport` (tex l.760) -/

/-- `cor:generaltransport` (`non_mf_group_notes.tex` l.760): general transport. Alias of
`GroupApproximation.KazhdanAsymptoticCommutant.compressionGroup_transport_both_anyUniverse`. -/
alias notes_cor_generaltransport := GroupApproximation.KazhdanAsymptoticCommutant.compressionGroup_transport_both_anyUniverse


/-! ## `thm:compression-radical` (tex l.796) -/

/-- `thm:compression-radical` (`non_mf_group_notes.tex` l.796): the compression radical. Alias
of
`GroupApproximation.KazhdanAsymptoticCommutant.manuscriptCompressionRadical_anyUniverse`. -/
alias notes_thm_compression_radical := GroupApproximation.KazhdanAsymptoticCommutant.manuscriptCompressionRadical_anyUniverse


/-! ## `thm:abstract-nk` (tex l.831) -/

/-- `thm:abstract-nk` (`non_mf_group_notes.tex` l.831): the abstract normal-Kazhdan
obstruction. Alias of
`GroupApproximation.ManuscriptExactWrappers.manuscriptAbstractNormalKazhdanObstruction`. -/
alias notes_thm_abstract_nk := GroupApproximation.ManuscriptExactWrappers.manuscriptAbstractNormalKazhdanObstruction


/-! ## `thm:normal-kazhdan` (tex l.939) -/

/-- `thm:normal-kazhdan` (`non_mf_group_notes.tex` l.939): the normal-Kazhdan obstruction.
Alias of
`GroupApproximation.ManuscriptExactWrappers.manuscriptNormalKazhdanObstruction_anyUniverse`. -/
alias notes_thm_normal_kazhdan := GroupApproximation.ManuscriptExactWrappers.manuscriptNormalKazhdanObstruction_anyUniverse


/-! ## `cor:intrinsic-nk` (tex l.963) -/

/-- `cor:intrinsic-nk` (`non_mf_group_notes.tex` l.963): the intrinsic normal-Kazhdan radical.
Alias of
`GroupApproximation.ManuscriptExactWrappers.manuscriptIntrinsicNormalKazhdanRadical_anyUniverse`. -/
alias notes_cor_intrinsic_nk := GroupApproximation.ManuscriptExactWrappers.manuscriptIntrinsicNormalKazhdanRadical_anyUniverse


/-! ## `thm:exactfd-intrinsic` (tex l.1000) -/

/-- `thm:exactfd-intrinsic` (`non_mf_group_notes.tex` l.1000): the exact finite-dimensional
intrinsic theorem. Alias of
`GroupApproximation.ManuscriptExactWrappers.manuscriptTheoremB`. -/
alias notes_thm_exactfd_intrinsic := GroupApproximation.ManuscriptExactWrappers.manuscriptTheoremB


/-! ## `cor:notRFD` (tex l.1027) -/

/-- `cor:notRFD` (`non_mf_group_notes.tex` l.1027): finite-dimensional consequences. Alias of
`GroupApproximation.LiteralFiniteDimensionalObstruction.manuscriptFiniteDimensionalConsequences`. -/
alias notes_cor_notRFD := GroupApproximation.LiteralFiniteDimensionalObstruction.manuscriptFiniteDimensionalConsequences


/-! ## `thm:cyclic` (tex l.1058) -/

/-- `thm:cyclic` (`non_mf_group_notes.tex` l.1058): cyclic calibration. Alias of
`GroupApproximation.LiteralCyclicCalibration.manuscriptCyclicCalibration`. -/
alias notes_thm_cyclic := GroupApproximation.LiteralCyclicCalibration.manuscriptCyclicCalibration


/-! ## `cor:scaling-family` (tex l.1193) -/

/-- `cor:scaling-family` (`non_mf_group_notes.tex` l.1193): the scaling family. Alias of
`GroupApproximation.ScalingFamilyEndpoint.manuscriptTheoremFamily`. -/
alias notes_cor_scaling_family := GroupApproximation.ScalingFamilyEndpoint.manuscriptTheoremFamily


/-! ## `def:radical` (tex l.1214) -/

/-- `def:radical` (`non_mf_group_notes.tex` l.1214): the MF radical. Alias of
`GroupApproximation.ManuscriptExactWrappers.manuscriptMFRadical`. -/
alias notes_def_radical := GroupApproximation.ManuscriptExactWrappers.manuscriptMFRadical


/-! ## `lem:portable` (tex l.1235) -/

/-- `lem:portable` (`non_mf_group_notes.tex` l.1235): radical portability. Alias of
`GroupApproximation.ManuscriptExactWrappers.manuscriptRadicalPortability`. -/
alias notes_lem_portable := GroupApproximation.ManuscriptExactWrappers.manuscriptRadicalPortability


/-! ## `prop:univquot` (tex l.1258) -/

/-- `prop:univquot` (`non_mf_group_notes.tex` l.1258): the universal MF quotient. Alias of
`GroupApproximation.ManuscriptExactWrappers.manuscriptUniversalMFQuotient`. -/
alias notes_prop_univquot := GroupApproximation.ManuscriptExactWrappers.manuscriptUniversalMFQuotient


/-! ## `cor:exactradical` (tex l.1301) -/

/-- `cor:exactradical` (`non_mf_group_notes.tex` l.1301): exact radical from a candidate
quotient. Alias of
`GroupApproximation.ManuscriptExactWrappers.manuscriptExactRadicalFromCandidateQuotient`. -/
alias notes_cor_exactradical := GroupApproximation.ManuscriptExactWrappers.manuscriptExactRadicalFromCandidateQuotient


/-! ## `cor:pullback` (tex l.1320) -/

/-- `cor:pullback` (`non_mf_group_notes.tex` l.1320): radical reduction to a quotient. Alias
of `GroupApproximation.ManuscriptExactWrappers.manuscriptRadicalReductionToQuotient`. -/
alias notes_cor_pullback := GroupApproximation.ManuscriptExactWrappers.manuscriptRadicalReductionToQuotient


/-! ## `thm:mf-radical-arithmetic` (tex l.1344) -/

/-- `thm:mf-radical-arithmetic` (`non_mf_group_notes.tex` l.1344): all three Pi02/Sigma02
clauses, through the repository's open microstate test. Alias of
`GroupApproximation.Full.NN02.manuscriptMFRadicalArithmetic`. -/
alias notes_thm_mf_radical_arithmetic := GroupApproximation.Full.NN02.manuscriptMFRadicalArithmetic

/-- `thm:mf-radical-arithmetic` (`non_mf_group_notes.tex` l.1344): the certificate semantics
of radical words. Alias of `GroupApproximation.Full.NN02.manuscriptRadicalWordSemantics`. -/
alias notes_thm_mf_radical_word_semantics := GroupApproximation.Full.NN02.manuscriptRadicalWordSemantics

/-- `thm:mf-radical-arithmetic` (`non_mf_group_notes.tex` l.1344): the three clauses through
the printed predicate `D(P,v,n,d)`; the decidability of `D` over the real closed field is
still a work order (NN02b/NN11b). Alias of
`GroupApproximation.Full.NN02b.manuscriptLiteralMFRadicalArithmetic`. -/
alias notes_thm_mf_radical_arithmetic_literal := GroupApproximation.Full.NN02b.manuscriptLiteralMFRadicalArithmetic

/-- `thm:mf-radical-arithmetic` (`non_mf_group_notes.tex` l.1344): the printed equivalence `v
∉ Res_MF ↔ ∀ n ∃ d, D(P,v,n,d)`. Alias of
`GroupApproximation.Full.NN02b.manuscriptLiteralRadicalWordSemantics`. -/
alias notes_thm_mf_radical_word_semantics_literal := GroupApproximation.Full.NN02b.manuscriptLiteralRadicalWordSemantics


/-! ## `thm:fixed-radical-membership` (tex l.1370) -/

/-- `thm:fixed-radical-membership` (`non_mf_group_notes.tex` l.1370): PARTIAL: the closed
package of the retraction clauses; the closed theorem still needs a finitely presented MF
group with undecidable word problem (NN03b, NN03c). Alias of
`GroupApproximation.Full.NN03.notesFixedRadicalMembershipClauses`. -/
alias notes_thm_fixed_radical_membership_clauses := GroupApproximation.Full.NN03.notesFixedRadicalMembershipClauses

/-- `thm:fixed-radical-membership` (`non_mf_group_notes.tex` l.1370): PARTIAL: the printed
shape for a presentation code whose group is MF with undecidable word problem (quantified
objects, not input binders). Alias of
`GroupApproximation.Full.NN03.notesFixedRadicalMembership_of_mfFactor`. -/
alias notes_thm_fixed_radical_membership_of_mfFactor := GroupApproximation.Full.NN03.notesFixedRadicalMembership_of_mfFactor

/-- `thm:fixed-radical-membership` (`non_mf_group_notes.tex` l.1370): the proof step "it is
amenable": every solvable group is amenable (Kharlampovich's group itself is lane NN03b).
Alias of `GroupApproximation.Full.Kharlampovich.isAmenable_of_isSolvable`. -/
alias notes_thm_fixed_radical_membership_solvable_amenable := GroupApproximation.Full.Kharlampovich.isAmenable_of_isSolvable


/-! ## `thm:fixed-radical-computer` (tex l.1403) -/

/-- `thm:fixed-radical-computer` (`non_mf_group_notes.tex` l.1403): the fixed-radical
computer. Alias of `GroupApproximation.MFRadicalComputer.closed_package`. -/
alias notes_thm_fixed_radical_computer := GroupApproximation.MFRadicalComputer.closed_package

/-- `thm:fixed-radical-computer` (`non_mf_group_notes.tex` l.1403): word membership in the
commutator residual. Alias of
`GroupApproximation.MFRadicalComputer.word_mem_commutator_residual`. -/
alias notes_thm_fixed_radical_computer_word := GroupApproximation.MFRadicalComputer.word_mem_commutator_residual


/-! ## `cor:nofaithful` (tex l.1440) -/

/-- `cor:nofaithful` (`non_mf_group_notes.tex` l.1440): no faithful corona target. Alias of
`GroupApproximation.LiteralNonMFConsequences.literal_no_faithful_corona_subalgebra_target`. -/
alias notes_cor_nofaithful := GroupApproximation.LiteralNonMFConsequences.literal_no_faithful_corona_subalgebra_target


/-! ## `lem:permanence` (tex l.1462) -/

/-- `lem:permanence` (`non_mf_group_notes.tex` l.1462): MF passes to subgroups. Alias of
`GroupApproximation.IsOperatorMF.subgroup`. -/
alias notes_lem_permanence_subgroup := GroupApproximation.IsOperatorMF.subgroup

/-- `lem:permanence` (`non_mf_group_notes.tex` l.1462): residually finite groups are MF. Alias
of `GroupApproximation.isOperatorMF_of_residuallyFinite`. -/
alias notes_lem_permanence_rf := GroupApproximation.isOperatorMF_of_residuallyFinite

/-- `lem:permanence` (`non_mf_group_notes.tex` l.1462): locally finite groups are MF. Alias of
`GroupApproximation.isOperatorMF_of_locallyFinite`. -/
alias notes_lem_permanence_locallyFinite := GroupApproximation.isOperatorMF_of_locallyFinite


/-! ## `cor:quotclosure` (tex l.1494) -/

/-- `cor:quotclosure` (`non_mf_group_notes.tex` l.1494): MF is not closed under quotients.
Alias of `GroupApproximation.LiteralMFQuotientControls.manuscriptQuotientNonclosure`. -/
alias notes_cor_quotclosure := GroupApproximation.LiteralMFQuotientControls.manuscriptQuotientNonclosure


/-! ## `thm:projection-collapse` (tex l.1510) -/

/-- `thm:projection-collapse` (`non_mf_group_notes.tex` l.1510): projection collapse. Alias of
`GroupApproximation.ProjectionCompressionCollapse.corona_projection_collapse`. -/
alias notes_thm_projection_collapse := GroupApproximation.ProjectionCompressionCollapse.corona_projection_collapse


/-! ## `def:invwitness` (tex l.1662) -/

/-- `def:invwitness` (`non_mf_group_notes.tex` l.1662): involutive collapse patterns. Alias of
`GroupApproximation.ManuscriptExactWrappers.manuscriptInvolutiveCollapsePattern`. -/
alias notes_def_invwitness := GroupApproximation.ManuscriptExactWrappers.manuscriptInvolutiveCollapsePattern


/-! ## `thm:collapse` (tex l.1689) -/

/-- `thm:collapse` (`non_mf_group_notes.tex` l.1689): involutive collapse. Alias of
`GroupApproximation.ManuscriptExactWrappers.manuscriptInvolutiveCollapse`. -/
alias notes_thm_collapse := GroupApproximation.ManuscriptExactWrappers.manuscriptInvolutiveCollapse


/-! ## `rem:torsion-collapse` (tex l.1716) -/

/-- `rem:torsion-collapse` (`non_mf_group_notes.tex` l.1716): torsion witnesses are
corona-invisible. Alias of
`GroupApproximation.TorsionSpectralCollapse.actualCoronaMFInvisible_of_torsionWitness`. -/
alias notes_rem_torsion_collapse_invisible := GroupApproximation.TorsionSpectralCollapse.actualCoronaMFInvisible_of_torsionWitness

/-- `rem:torsion-collapse` (`non_mf_group_notes.tex` l.1716): the torsion collapse defect lies
in the MF residual. Alias of
`GroupApproximation.TorsionSpectralCollapse.torsionCollapseDefect_le_actualCoronaMFResidual_of_kazhdan`. -/
alias notes_rem_torsion_collapse_le := GroupApproximation.TorsionSpectralCollapse.torsionCollapseDefect_le_actualCoronaMFResidual_of_kazhdan

/-- `rem:torsion-collapse` (`non_mf_group_notes.tex` l.1716): the MF residual equals the
torsion collapse defect. Alias of
`GroupApproximation.TorsionSpectralCollapse.actualCoronaMFResidual_eq_torsionCollapseDefect_of_kazhdan`. -/
alias notes_rem_torsion_collapse_eq := GroupApproximation.TorsionSpectralCollapse.actualCoronaMFResidual_eq_torsionCollapseDefect_of_kazhdan


/-! ## `cor:collapsequot` (tex l.1801) -/

/-- `cor:collapsequot` (`non_mf_group_notes.tex` l.1801): collapse radical reduction. Alias of
`GroupApproximation.ManuscriptExactWrappers.manuscriptCollapseRadicalReduction`. -/
alias notes_cor_collapsequot := GroupApproximation.ManuscriptExactWrappers.manuscriptCollapseRadicalReduction


/-! ## `thm:exact-mf-residual` (tex l.1826) -/

/-- `thm:exact-mf-residual` (`non_mf_group_notes.tex` l.1826): the defect clauses `D =
N_conj`, `E/D ≅ Σ *_B (B × C₂)`, `D ≤ Res_MF(E)`. Alias of
`GroupApproximation.Full.NN01.exactResidualDefects`. -/
alias notes_thm_exact_mf_residual_defects := GroupApproximation.Full.NN01.exactResidualDefects

/-- `thm:exact-mf-residual` (`non_mf_group_notes.tex` l.1826): PARTIAL: the printed theorem is
equivalent to `IsOperatorMF TerminalAmalgam`, which is not yet proved (NN01b, Shulman
amalgam). Alias of `GroupApproximation.Full.NN01.notesExactMFResidual_iff`. -/
alias notes_thm_exact_mf_residual_iff := GroupApproximation.Full.NN01.notesExactMFResidual_iff

/-- `thm:exact-mf-residual` (`non_mf_group_notes.tex` l.1826): PARTIAL: the closed package of
everything proved about the residual. Alias of
`GroupApproximation.Full.NN01.exactResidual_state`. -/
alias notes_thm_exact_mf_residual_state := GroupApproximation.Full.NN01.exactResidual_state

/-- `thm:exact-mf-residual` (`non_mf_group_notes.tex` l.1826): exact finite routes to the MF
clause are refuted. Alias of `GroupApproximation.Full.NN01.exactResidualObstruction`. -/
alias notes_thm_exact_mf_residual_obstruction := GroupApproximation.Full.NN01.exactResidualObstruction


/-! ## `thm:notes-spectral-motion` (tex l.1904) -/

/-- `thm:notes-spectral-motion` (`non_mf_group_notes.tex` l.1904): spectral compression. Alias
of `GroupApproximation.SpectralPaper.spectralCompressionTheorem`. -/
alias notes_thm_notes_spectral_motion := GroupApproximation.SpectralPaper.spectralCompressionTheorem

/-- `thm:notes-spectral-motion` (`non_mf_group_notes.tex` l.1904): zero-dimensional spectral
collapse. Alias of
`GroupApproximation.SpectralPaper.zeroDimensionalSpectralCollapseTheorem`. -/
alias notes_thm_notes_spectral_motion_zero_dim := GroupApproximation.SpectralPaper.zeroDimensionalSpectralCollapseTheorem


/-! ## `thm:notes-visible-quotient` (tex l.1964) -/

/-- `thm:notes-visible-quotient` (`non_mf_group_notes.tex` l.1964): the visible quotient `Φ_K
: W_K → P_K` for finite `K`. Alias of `GroupApproximation.Full.NN04.notesVisibleQuotient`. -/
alias notes_thm_notes_visible_quotient := GroupApproximation.Full.NN04.notesVisibleQuotient

/-- `thm:notes-visible-quotient` (`non_mf_group_notes.tex` l.1964): precomposition with `Φ_K`
is bijective on every printed class of targets. Alias of
`GroupApproximation.Full.NN04.notesVisibleQuotient_precomp_bijective`. -/
alias notes_thm_notes_visible_quotient_precomp := GroupApproximation.Full.NN04.notesVisibleQuotient_precomp_bijective


/-! ## `cor:notes-a5-relation` (tex l.2053) -/

/-- `cor:notes-a5-relation` (`non_mf_group_notes.tex` l.2053): the corollary for the printed
group. Alias of `GroupApproximation.Full.NN05.notesA5RelationLiteral`. -/
alias notes_cor_notes_a5_relation := GroupApproximation.Full.NN05.notesA5RelationLiteral

/-- `cor:notes-a5-relation` (`non_mf_group_notes.tex` l.2053): the corollary at the wreath
model. Alias of `GroupApproximation.Full.NN05.notesA5Relation`. -/
alias notes_cor_notes_a5_relation_model := GroupApproximation.Full.NN05.notesA5Relation

/-- `cor:notes-a5-relation` (`non_mf_group_notes.tex` l.2053): `G_*` is MF. Alias of
`GroupApproximation.Full.NN05.gstar_isOperatorMF`. -/
alias notes_cor_notes_a5_gstar_mf := GroupApproximation.Full.NN05.gstar_isOperatorMF


/-! ## `thm:notes-abelian-boundary` (tex l.2078) -/

/-- `thm:notes-abelian-boundary` (`non_mf_group_notes.tex` l.2078): PARTIAL: MF implies
torsion-free; the converse (slow-bump corona) is in progress (NN06). Alias of
`GroupApproximation.Full.NN06.isAddTorsionFree_of_isOperatorMF`. -/
alias notes_thm_notes_abelian_boundary_torsionFree := GroupApproximation.Full.NN06.isAddTorsionFree_of_isOperatorMF

/-- `thm:notes-abelian-boundary` (`non_mf_group_notes.tex` l.2078): PARTIAL: torsion prevents
MF. Alias of `GroupApproximation.Full.NN06.not_isOperatorMF_of_not_isAddTorsionFree`. -/
alias notes_thm_notes_abelian_boundary_torsion := GroupApproximation.Full.NN06.not_isOperatorMF_of_not_isAddTorsionFree


/-! ## `lem:faithfultrace` (tex l.2166) -/

/-- `lem:faithfultrace` (`non_mf_group_notes.tex` l.2166): faithful trace and stable
finiteness. Alias of
`GroupApproximation.ManuscriptExactWrappers.manuscriptFaithfulTraceAndStableFiniteness`. -/
alias notes_lem_faithfultrace := GroupApproximation.ManuscriptExactWrappers.manuscriptFaithfulTraceAndStableFiniteness


/-! ## `prop:blocknormalform` (tex l.2349) -/

/-- `prop:blocknormalform` (`non_mf_group_notes.tex` l.2349): site lamp images (the
normal-form equivalence is the data `LiteralBlockNormalForm.markedGroupEquivModel`). Alias
of `GroupApproximation.LiteralBlockNormalForm.manuscriptSiteLampImage`. -/
alias notes_prop_blocknormalform_site_lamp := GroupApproximation.LiteralBlockNormalForm.manuscriptSiteLampImage

/-- `prop:blocknormalform` (`non_mf_group_notes.tex` l.2349): the normal form sends the mark
to the central lamp. Alias of `GroupApproximation.LiteralBlockNormalForm.toModel_mark`. -/
alias notes_prop_blocknormalform_mark := GroupApproximation.LiteralBlockNormalForm.toModel_mark

/-- `prop:blocknormalform` (`non_mf_group_notes.tex` l.2349): finite-level site orbits. Alias
of `GroupApproximation.LiteralBlockNormalForm.manuscriptFiniteLevelSiteOrbit`. -/
alias notes_prop_blocknormalform_orbit := GroupApproximation.LiteralBlockNormalForm.manuscriptFiniteLevelSiteOrbit


/-! ## `lem:window` (tex l.2426) -/

/-- `lem:window` (`non_mf_group_notes.tex` l.2426): residually finite windows. Alias of
`GroupApproximation.BlockCliffordTowerSofic.manuscriptResiduallyFiniteWindow`. -/
alias notes_lem_window := GroupApproximation.BlockCliffordTowerSofic.manuscriptResiduallyFiniteWindow


/-! ## `prop:horn` (tex l.2519) -/

/-- `prop:horn` (`non_mf_group_notes.tex` l.2519): the universal Horn sentence. Alias of
`GroupApproximation.LiteralUniversalHorn.manuscriptLiteralUniversalHorn`. -/
alias notes_prop_horn := GroupApproximation.LiteralUniversalHorn.manuscriptLiteralUniversalHorn


/-! ## `cor:undecidable` (tex l.2562) -/

/-- `cor:undecidable` (`non_mf_group_notes.tex` l.2562): the word problem is undecidable.
Alias of `GroupApproximation.Computability.not_computablePred_wordProblemPred`. -/
alias notes_cor_undecidable_wordProblem := GroupApproximation.Computability.not_computablePred_wordProblemPred

/-- `cor:undecidable` (`non_mf_group_notes.tex` l.2562): MF recognition is not computable.
Alias of `GroupApproximation.Computability.operatorMF_recognition_not_computable`. -/
alias notes_cor_undecidable_recognition := GroupApproximation.Computability.operatorMF_recognition_not_computable

/-- `cor:undecidable` (`non_mf_group_notes.tex` l.2562): the word problem is r.e.. Alias of
`GroupApproximation.WordProblemRE.rePred_wordProblemPred`. -/
alias notes_cor_undecidable_wordProblem_re := GroupApproximation.WordProblemRE.rePred_wordProblemPred

/-- `cor:undecidable` (`non_mf_group_notes.tex` l.2562): the non-MF side is not r.e.. Alias of
`GroupApproximation.WordProblemRE.operatorMF_negative_side_not_re`. -/
alias notes_cor_undecidable_negative_not_re := GroupApproximation.WordProblemRE.operatorMF_negative_side_not_re

/-- `cor:undecidable` (`non_mf_group_notes.tex` l.2562): the unconditional endpoint of the
transfer step: MF recognition on presentation codes is undecidable, with the word-problem
premise discharged inside the proof. Alias of
`GroupApproximation.Full.NN13AR.operatorMF_recognition_undecidable`. -/
alias notes_cor_undecidable_transfer := GroupApproximation.Full.NN13AR.operatorMF_recognition_undecidable

/-- `cor:undecidable` (`non_mf_group_notes.tex` l.2562): the unconditional endpoint of the
transfer step for the negative side: the non-MF codes are not recursively enumerable.
Alias of `GroupApproximation.Full.NN13AR.operatorMF_negative_side_not_re`. -/
alias notes_cor_undecidable_negative_side_not_re := GroupApproximation.Full.NN13AR.operatorMF_negative_side_not_re

/-- `cor:undecidable` (`non_mf_group_notes.tex` l.2562): the printed corollary. Alias of
`GroupApproximation.Full.NN11.notesUndecidable`. -/
alias notes_cor_undecidable_notes := GroupApproximation.Full.NN11.notesUndecidable

/-- `cor:undecidable` (`non_mf_group_notes.tex` l.2562): the printed corollary with its proof
steps. Alias of `GroupApproximation.Full.NN11.notesUndecidableWithProof`. -/
alias notes_cor_undecidable_notes_with_proof := GroupApproximation.Full.NN11.notesUndecidableWithProof

/-- `cor:undecidable` (`non_mf_group_notes.tex` l.2562): MF is a Markov property. Alias of
`GroupApproximation.Full.NN11.notesMarkovProperty`. -/
alias notes_cor_undecidable_markov := GroupApproximation.Full.NN11.notesMarkovProperty

/-- `cor:undecidable` (`non_mf_group_notes.tex` l.2562): the Adian-Rabin map of the proof.
Alias of `GroupApproximation.Full.NN11.notesAdianRabinMap`. -/
alias notes_cor_undecidable_adianRabin := GroupApproximation.Full.NN11.notesAdianRabinMap

/-- `cor:undecidable` (`non_mf_group_notes.tex` l.2562): the complement of the word problem
many-one reduces to non-MF codes through `E`. Alias of
`GroupApproximation.Full.NN11.wordProblemCompl_manyOneReduces_nonMF_viaE`. -/
alias notes_cor_undecidable_reduction_viaE := GroupApproximation.Full.NN11.wordProblemCompl_manyOneReduces_nonMF_viaE


/-! ## `thm:mf-arithmetic` (tex l.2626) -/

/-- `thm:mf-arithmetic` (`non_mf_group_notes.tex` l.2626): the classification, through the
repository's matrix checker (the real-closed-field sentence of the proof is NN11b). Alias
of `GroupApproximation.Full.NN11.notesMFArithmetic`. -/
alias notes_thm_mf_arithmetic := GroupApproximation.Full.NN11.notesMFArithmetic

/-- `thm:mf-arithmetic` (`non_mf_group_notes.tex` l.2626): `MF_fp` is Pi02 and not Pi01. Alias
of `GroupApproximation.Full.NN11.mfCode_pi02_not_pi01`. -/
alias notes_thm_mf_arithmetic_pi02 := GroupApproximation.Full.NN11.mfCode_pi02_not_pi01

/-- `thm:mf-arithmetic` (`non_mf_group_notes.tex` l.2626): `NONMF_fp` is Sigma02 and not
Sigma01. Alias of `GroupApproximation.Full.NN11.nonMFCode_sigma02_not_sigma01`. -/
alias notes_thm_mf_arithmetic_sigma02 := GroupApproximation.Full.NN11.nonMFCode_sigma02_not_sigma01


/-! ## `thm:torsionfree` (tex l.2757) -/

/-- `thm:torsionfree` (`non_mf_group_notes.tex` l.2757): PARTIAL: every algebraic and operator
step, for a configuration and a routed quotient; existence of both is NN07a/NN07b and
NN08b. Alias of
`GroupApproximation.Full.NN07b.NotesConfiguration.exists_selfRadical_of_routedQuotient`. -/
alias notes_thm_torsionfree_routed := GroupApproximation.Full.NN07b.NotesConfiguration.exists_selfRadical_of_routedQuotient


/-! ## `rem:ff-realization` (tex l.2818) -/

/-- `rem:ff-realization` (`non_mf_group_notes.tex` l.2818): the remark after its first
sentence, at the printed datum; existence of the [FFF] group `P` is NN08b. Alias of
`GroupApproximation.Full.NN08.ffRealization`. -/
alias notes_rem_ff_realization := GroupApproximation.Full.NN08.ffRealization

/-- `rem:ff-realization` (`non_mf_group_notes.tex` l.2818): the remark for a given datum.
Alias of `GroupApproximation.Full.NN08.remFFRealization`. -/
alias notes_rem_ff_realization_datum := GroupApproximation.Full.NN08.remFFRealization

/-- `rem:ff-realization` (`non_mf_group_notes.tex` l.2818): realization from a universal
group. Alias of `GroupApproximation.RealizationFromUniversalGroup.realization`. -/
alias notes_rem_ff_realization_universal := GroupApproximation.RealizationFromUniversalGroup.realization

/-- `rem:ff-realization` (`non_mf_group_notes.tex` l.2818): the Clifford coset representation
gives w != 1 in E(P,alpha,a). Alias of `GroupApproximation.Full.NN08.ePα_mark_ne_one`. -/
alias notes_rem_ff_realization_mark_ne_one := GroupApproximation.Full.NN08.ePα_mark_ne_one

/-- `rem:ff-realization` (`non_mf_group_notes.tex` l.2818): E(P,alpha,a) has torsion. Alias of
`GroupApproximation.Full.NN08.ePα_has_torsion`. -/
alias notes_rem_ff_realization_torsion := GroupApproximation.Full.NN08.ePα_has_torsion

/-- `rem:ff-realization` (`non_mf_group_notes.tex` l.2818): E(P,alpha,a) is not MF when P has
property (T). Alias of `GroupApproximation.Full.NN08.ePα_not_isOperatorMF`. -/
alias notes_rem_ff_realization_not_mf := GroupApproximation.Full.NN08.ePα_not_isOperatorMF


/-! ## `prose:Esofic` (tex l.439) -/

/-- `prose:Esofic` (`non_mf_group_notes.tex` l.439): `E_0` is LEF and `E` is a split extension
of `E_0` by `Z`. Alias of `GroupApproximation.Full.NN12.e0_printed`. -/
alias notes_prose_E0_lef := GroupApproximation.Full.NN12.e0_printed


/-! ## `prose:findim` (tex l.987) -/

/-- `prose:findim` (`non_mf_group_notes.tex` l.987): `E` is a group of Deligne type. Alias of
`GroupApproximation.Full.NN12.markedGroup_isDeligneType`. -/
alias notes_prose_deligne_type := GroupApproximation.Full.NN12.markedGroup_isDeligneType

/-- `prose:findim` (`non_mf_group_notes.tex` l.987): the finite-dimensional paragraph. Alias
of `GroupApproximation.Full.NN12.findim_paragraph_printed`. -/
alias notes_prose_findim_paragraph := GroupApproximation.Full.NN12.findim_paragraph_printed


/-! ## `prose:sharpness` (tex l.1163) -/

/-- `prose:sharpness` (`non_mf_group_notes.tex` l.1163): PARTIAL: the realized Clifford
quotient paragraph, except "So it is MF" (NN10b). Alias of
`GroupApproximation.Full.NN10.notesRealizedCliffordQuotient`. -/
alias notes_prose_realized_clifford_quotient := GroupApproximation.Full.NN10.notesRealizedCliffordQuotient

/-- `prose:sharpness` (`non_mf_group_notes.tex` l.1163): the realized quotients are amenable.
Alias of `GroupApproximation.Full.NN10.realizedCliffordQuotient_isAmenable`. -/
alias notes_prose_realized_clifford_quotient_amenable := GroupApproximation.Full.NN10.realizedCliffordQuotient_isAmenable


/-! ## `prose:marked-obstruction` (tex l.733) -/

/-- `prose:marked-obstruction` (`non_mf_group_notes.tex` l.733): the finite normal subgroup
remark. Alias of `GroupApproximation.Full.NN12.finiteNormal_remark`. -/
alias notes_prose_finite_normal_remark := GroupApproximation.Full.NN12.finiteNormal_remark

/-- `prose:marked-obstruction` (`non_mf_group_notes.tex` l.733): the central involution
remark. Alias of `GroupApproximation.Full.NN12.centralInvolution_remark`. -/
alias notes_prose_central_involution_remark := GroupApproximation.Full.NN12.centralInvolution_remark


/-! ## `prose:blocknormalform` (tex l.2349) -/

/-- `prose:blocknormalform` (`non_mf_group_notes.tex` l.2349): the block comparison after the
normal form. Alias of `GroupApproximation.Full.NN12.blockComparison_printed`. -/
alias notes_prose_block_comparison := GroupApproximation.Full.NN12.blockComparison_printed


/-! ## `prose:exactness` (tex l.2487) -/

/-- `prose:exactness` (`non_mf_group_notes.tex` l.2487): finite free products of finite groups
have property A. Alias of `GroupApproximation.Full.NN09.hasPropertyA_coprodI`. -/
alias notes_prose_free_product_propertyA := GroupApproximation.Full.NN09.hasPropertyA_coprodI

/-- `prose:exactness` (`non_mf_group_notes.tex` l.2487): the block Clifford group has property
A. Alias of `GroupApproximation.Full.NN09.hasPropertyA_blockClifford`. -/
alias notes_prose_block_clifford_propertyA := GroupApproximation.Full.NN09.hasPropertyA_blockClifford

/-- `prose:exactness` (`non_mf_group_notes.tex` l.2487): amenable groups have property A
(Folner weights), a step toward the GHW exactness paragraph (lanes NN09b, NN09c). Alias of
`GroupApproximation.Full.NN09b.hasPropertyA_of_isAmenable`. -/
alias notes_prose_amenable_propertyA := GroupApproximation.Full.NN09b.hasPropertyA_of_isAmenable

end GroupApproximation.Full.NNRoot
