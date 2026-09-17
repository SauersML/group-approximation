import GroupApproximation.Sofic.CliffordWitnessDirectDefect
import GroupApproximation.Sofic.CentralInvolutionSubgroup
import GroupApproximation.Sofic.NormalKazhdanMFRadical
import GroupApproximation.Manuscript.NonMFSentences.IntroWitnessSignSentence
import GroupApproximation.Monsters.AffineSL3Doubling
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.NormMFCoronaRadical
import GroupApproximation.Sofic.NormMFResidualDetector
import GroupApproximation.Sofic.ChosenNonMFTheorem
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion
import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingProperIsometry
import GroupApproximation.Meta.AxiomGuard

/-!
# Mathematics asserted in the Related work and Origin sections

`non_mf_groups_exist.tex`.

**Related work, lines 336--339** (census row `213a6657c8ff`):

> Theorem [compression-criterion] uses the configuration of the nonsofic
> construction [OAI, Proposition 2.3]: a property-(T) subgroup L conjugated
> into itself by an element u, and an element c commuting with L whose
> conjugate ucu^{-1} does not.

`manuscriptSentence_compressionCriterionConfiguration`: the configuration
occurs (in the rank-twelve group, `L = corner`, `u = tau`, `c = c`; the
failure of `ucu⁻¹` to commute with `L` is `⁅tau c tau⁻¹, ell⁆ = defect ≠ 1`),
together with the compression criterion that uses it.

**Origin and authorship, lines 2239--2242** (rows `3113d5d90053`,
`2b5a42f87cb2`):

> Sol answered with an MF counterexample: every norm-matrix model of the
> Clifford-twisted wreath product kills the Clifford sign.  That was on
> August 9.  Also on August 9, the models proved that the maximal group
> C*-algebra of a strictly compressed Kazhdan group is infinite.

* `manuscriptSentence_normMatrixModelsKillCliffordSign`: for the Clifford
  witness of the proper self-embedding `alpha` of the affine `SL₃` Kazhdan
  group, the Clifford sign is nontrivial, every homomorphism into an
  operator-norm matrix ultraproduct kills it, and the group is not MF.  Route:
  the compression criterion puts the finite normal sign subgroup, which lies
  in the printed defect of the Kazhdan base, inside the corona MF residual,
  which equals the norm-MF residual.
* `manuscriptSentence_strictlyCompressedKazhdanMaximalInfinite`: if a Kazhdan
  subgroup `Γ` is strictly compressed by conjugation, `C*_max(G)` contains a
  proper isometry and is not Dedekind finite, through
  `FullDefectRing.properIsometry_of_strictCompression`.

**Origin and authorship, lines 2244--2246** (row `1778c11e19e3`):

> By August 12 the models had reduced the obstruction to one commutator in a
> finitely presented group and had proved in Lean that it is not MF.

`manuscriptSentence_oneCommutatorFinitelyPresentedNotMF`: the chosen marked
presentation is finitely presented, its mark is one nontrivial commutator
killed by every norm-matrix model, and the group is not operator MF.

Dates and authorship are provenance and are not formalized.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace AuditRelated

open scoped commutatorElement

/-- **tex 336--339.**  The configuration of [OAI, Proposition 2.3] occurs:
a property-(T) subgroup `L`, an element `u` conjugating `L` into itself, and
an element `c` commuting with `L` whose conjugate `u c u⁻¹` does not; and the
compression criterion built on it holds. -/
theorem manuscriptSentence_compressionCriterionConfiguration :
    (∃ (G : Type) (_ : Group G) (L : Subgroup G) (u c : G),
      HasKazhdanPropertyT.{0, 0} ↥L ∧
        (∀ l ∈ L, u * l * u⁻¹ ∈ L) ∧
        (∀ l ∈ L, Commute c l) ∧
        ¬ ∀ l ∈ L, Commute (u * c * u⁻¹) l) ∧
      OneSidedMFRadical.OneSidedCompressionCriterion := by
  refine ⟨⟨OneSidedMFRadical.RankTwelveEndpoint.H, inferInstance,
    OneSidedMFRadical.RankTwelveEndpoint.corner,
    OneSidedMFRadical.RankTwelveEndpoint.tau,
    OneSidedMFRadical.RankTwelveEndpoint.c,
    OneSidedMFRadical.RankTwelveEndpoint.corner_hasKazhdanPropertyT,
    OneSidedMFRadical.RankTwelveEndpoint.tau_compresses_corner,
    OneSidedMFRadical.RankTwelveEndpoint.c_commutes_corner, ?_⟩,
    OneSidedMFRadical.manuscriptOneSidedCompressionCriterion⟩
  intro h
  apply OneSidedMFRadical.RankTwelveEndpoint.defect_ne_one
  rw [← OneSidedMFRadical.RankTwelveEndpoint.tau_c_commutator_ell]
  exact commutatorElement_eq_one_iff_commute.mpr
    (h OneSidedMFRadical.RankTwelveEndpoint.ell
      OneSidedMFRadical.RankTwelveEndpoint.ell_mem_corner)

/-- **tex 2240--2242.**  The maximal group C*-algebra of a group in which a
Kazhdan subgroup is strictly compressed by conjugation is infinite: it
contains a proper isometry and is not Dedekind finite. -/
theorem manuscriptSentence_strictlyCompressedKazhdanMaximalInfinite :
    ∀ (G : Type) [Group G] (Γ : Subgroup G) (u : G),
      HasKazhdanPropertyT.{0, 0} ↥Γ →
        Γ.map (MulAut.conj u).toMonoidHom < Γ →
          (∃ v : MaximalGroupCStar G, star v * v = 1 ∧ ¬ IsUnit v) ∧
            ¬ IsDedekindFiniteMonoid (MaximalGroupCStar G) := by
  intro G _ Γ u hT hlt
  have h := OneSidedMFRadical.FullDefectRing.properIsometry_of_strictCompression
    Γ u hT hlt
  exact ⟨h.1, h.2.1⟩

/-- **tex 2244--2246.**  The obstruction is one commutator in a finitely
presented group: the commutator is nontrivial, every operator-norm matrix
model kills it, and the group is not MF. -/
theorem manuscriptSentence_oneCommutatorFinitelyPresentedNotMF :
    ∃ (G : Type) (_ : Group G) (x y : G),
      Group.IsFinitelyPresented G ∧ ⁅x, y⁆ ≠ 1 ∧ NormMFInvisible ⁅x, y⁆ ∧
        ¬ IsOperatorMF G := by
  refine ⟨ChosenMarkedPresentation.MarkedGroup, inferInstance,
    ChosenMarkedPresentation.wordInMarkedGroup
      ChosenMarkedPresentation.displacedLampWord,
    ChosenMarkedPresentation.wordInMarkedGroup
      (ChosenMarkedPresentation.omittedWord *
        ChosenMarkedPresentation.displacedLampWord *
        ChosenMarkedPresentation.omittedWord⁻¹), ?_⟩
  have hmark : ChosenMarkedPresentation.mark =
      ⁅ChosenMarkedPresentation.wordInMarkedGroup
          ChosenMarkedPresentation.displacedLampWord,
        ChosenMarkedPresentation.wordInMarkedGroup
          (ChosenMarkedPresentation.omittedWord *
            ChosenMarkedPresentation.displacedLampWord *
            ChosenMarkedPresentation.omittedWord⁻¹)⁆ :=
    map_commutatorElement ChosenMarkedPresentation.wordInMarkedGroup _ _
  rw [← hmark]
  exact ⟨ChosenNonMFTheorem.chosenFinitelyPresented_not_isOperatorMF.1,
    ChosenMarkedPresentation.mark_ne_one,
    ChosenNonMFTheorem.mark_normMFInvisible,
    ChosenNonMFTheorem.chosenFinitelyPresented_not_isOperatorMF.2⟩

/-- The Clifford sign of the witness of a proper self-embedding of a countable
Kazhdan group lies in the norm-MF residual. -/
theorem cliffordSign_mem_normMFResidual {Γ : Type} [Group Γ] [Countable Γ]
    (α : Γ →* Γ) (hα : Function.Injective α) {a : Γ} (ha : a ∉ Set.range α)
    (hT : HasKazhdanPropertyT.{0, 0} Γ) :
    MarkedCompression.signAmbient α hα ∈
      normMFResidual (MarkedCompression.Ambient α hα) := by
  have hcriterion :=
    OneSidedMFRadical.manuscriptOneSidedCompressionCriterion
      (MarkedCompression.Ambient α hα)
      (CliffordWitnessDirectDefect.baseSubgroup α hα)
      (CliffordWitnessDirectDefect.baseSubgroup_hasKazhdanPropertyT α hα hT)
  have hK : HasKazhdanPropertyT.{0, 0} (CliffordWitnessDirectDefect.signSubgroup α hα) :=
    hasKazhdanPropertyT_of_finite (CliffordWitnessDirectDefect.signSubgroup α hα)
  have hsign : MarkedCompression.signAmbient α hα ∈
      manuscriptCoronaMFResidual (MarkedCompression.Ambient α hα) :=
    hcriterion.1 (CliffordWitnessDirectDefect.signSubgroup α hα) hK
      (CliffordWitnessDirectDefect.signSubgroup_le_printedDefect α hα ha)
      (involution_mem_centralInvolutionSubgroup _ _)
  rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual,
    actualCoronaMFResidual_eq_coronaMFResidual,
    coronaMFResidual_eq_normMFResidual] at hsign
  exact hsign

/-- **tex 2239--2240.**  The Clifford witness is an MF counterexample: its
Clifford sign is nontrivial, every norm-matrix model (every homomorphism into
an operator-norm matrix ultraproduct) kills it, and the group is not MF. -/
theorem manuscriptSentence_normMatrixModelsKillCliffordSign :
    ¬ IsOperatorMF
        (MarkedCompression.Ambient AffineSL3Doubling.alpha
          AffineSL3Doubling.alpha_injective) ∧
      MarkedCompression.signAmbient AffineSL3Doubling.alpha
          AffineSL3Doubling.alpha_injective ≠ 1 ∧
      ∀ (I : Type) (U : Ultrafilter I) (X : I → FiniteModel)
        (rho : MarkedCompression.Ambient AffineSL3Doubling.alpha
          AffineSL3Doubling.alpha_injective →* UniversalWeakMF U X),
        rho (MarkedCompression.signAmbient AffineSL3Doubling.alpha
          AffineSL3Doubling.alpha_injective) = 1 := by
  haveI : Countable AffineSL3Doubling.Gamma :=
    NonMFSentences.IntroWitnessSignSentence.gamma_countable
  refine ⟨CliffordWitnessDirectDefect.not_isOperatorMF AffineSL3Doubling.alpha
      AffineSL3Doubling.alpha_injective AffineSL3Doubling.a_not_mem_range
      NonMFSentences.IntroWitnessSignSentence.gamma_hasKazhdanPropertyT,
    MarkedCompression.signAmbient_ne_one _ _, ?_⟩
  intro I U X rho
  exact map_eq_one_of_mem_normMFResidual U X rho
    (cliffordSign_mem_normMFResidual AffineSL3Doubling.alpha
      AffineSL3Doubling.alpha_injective AffineSL3Doubling.a_not_mem_range
      NonMFSentences.IntroWitnessSignSentence.gamma_hasKazhdanPropertyT)

end AuditRelated
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.AuditRelated.manuscriptSentence_compressionCriterionConfiguration
#audit_axioms GroupApproximation.Manuscript.NonMF.AuditRelated.manuscriptSentence_strictlyCompressedKazhdanMaximalInfinite
#audit_axioms GroupApproximation.Manuscript.NonMF.AuditRelated.manuscriptSentence_oneCommutatorFinitelyPresentedNotMF
#audit_axioms GroupApproximation.Manuscript.NonMF.AuditRelated.cliffordSign_mem_normMFResidual
#audit_axioms GroupApproximation.Manuscript.NonMF.AuditRelated.manuscriptSentence_normMatrixModelsKillCliffordSign
