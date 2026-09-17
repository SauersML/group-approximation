import GroupApproximation.Manuscript.OneSidedMFRadical.UnitGroupHeadline
import GroupApproximation.Manuscript.OneSidedMFRadical.UnitGroupRankDescent
import GroupApproximation.Manuscript.OneSidedMFRadical.MFHomKernel
import GroupApproximation.Manuscript.NonMFSentences.IntroSentences
import GroupApproximation.Sofic.HyperlinearReduction
import GroupApproximation.Sofic.LiteralWitnessConsequences
import GroupApproximation.Sofic.CliffordWitnessHSRemark
import GroupApproximation.Endpoint.MainResults
import GroupApproximation.Meta.AxiomGuard

/-!
# Introduction: the MF radical, the existence sentence, and the OpenAI attribution

This module covers three sentences from the Introduction of
`non_mf_groups_exist.tex`.

## The MF radical (census line 122, key `10e027681ba5`)

> Write `Rad_MF(G) = ⋂ {ker f : f : G → M, M an MF group}` for the *MF radical*
> of `G`.

The listed declaration `manuscriptSentence_mfRadicalFormula` describes membership
in `manuscriptCoronaMFResidual` for countable `G` by quantifying over countable
CDE-MF targets. The printed definition is the intersection over *all* MF targets,
and `MFQuotientUnits.mfHomKernel` is literally that intersection.
`manuscriptSentence_mfRadicalDefinition` states membership in that intersection
for every `G`. It also shows that for countable `G` the intersection equals
`manuscriptCoronaMFResidual G`.

Proof route for the equality. An operator-MF target is CDE-MF once it is
countable (`isCDEOperatorMF_iff_isOperatorMF`). Conversely, a homomorphism
`f : G → M` into an arbitrary operator-MF group factors through `f.range`. That
range is countable because `G` is, and it is operator-MF because MF passes to
subgroups (`FullDefectRankTwo.isOperatorMF_of_injective`).

## Existence of the two kinds of counterexample (census line 126, key `5a7e84235409`)

> We construct groups for which every homomorphism to an MF group is trivial, as
> well as a sofic group with a nontrivial element killed by every MF
> homomorphism.

* First clause, at `H = L_{𝔽₂}(1,2)^×`. `H` is nontrivial, and every homomorphism
  from `H` to an operator-MF group is trivial. The headline
  `UnitGroupHeadline.manuscriptUnitGroupHeadline` supplies nontriviality, finite
  generation (so `H` is countable) and the killing of every homomorphism to a
  countable CDE-MF group. The range argument above extends this to arbitrary
  operator-MF targets.
* Second clause, at the affine–Clifford witness `W = WitnessGroup`. `W` is sofic
  (`LiteralWitnessConsequences.witnessGroup_isSofic`), and the central sign
  `ε = witnessSign` is nontrivial (`CliffordWitnessHSRemark.witnessSign_ne_one`).
  Every homomorphism to an operator-MF group kills it
  (`CliffordWitnessDirectDefect.map_sign_eq_one_of_isOperatorMF_target`, at the
  proper self-embedding `conjD` of the property-(T) base `gammaBar`).

## The OpenAI attribution (census line 148, key `374637bc6ac7`)

> OpenAI used this group to construct the first nonsofic group [OAI, Chapter 3].

The attribution asserts mathematics: a nonsofic group comes from
`H = L_{𝔽₂}(1,2)^×`. The repository proves outright that `H` itself is not
sofic (`binaryLeavittUnits_not_isSofic` at `k = 𝔽₂`).
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace AuditIntro

/-! ## From countable CDE-MF targets to all operator-MF targets -/

/-- If an element of a countable group is killed by every homomorphism to a
countable CDE-MF group, it is killed by every homomorphism to any operator-MF
group: factor through the (countable, operator-MF) range. -/
theorem map_eq_one_of_isOperatorMF_of_killsCountableCDE {G : Type} [Group G]
    [Countable G] {x : G}
    (h : ∀ (M : Type) [Group M] [Countable M], IsCDEOperatorMF M →
      ∀ f : G →* M, f x = 1)
    {M : Type} [Group M] (hM : IsOperatorMF M) (f : G →* M) : f x = 1 := by
  haveI : Countable ↥f.range := f.rangeRestrict_surjective.countable
  have hrange : IsCDEOperatorMF ↥f.range :=
    (isCDEOperatorMF_iff_isOperatorMF ↥f.range).mpr
      (OneSidedMFRadical.FullDefectRankTwo.isOperatorMF_of_injective f.range.subtype
        f.range.subtype_injective hM)
  have hx : f.rangeRestrict x = 1 := h ↥f.range hrange f.rangeRestrict
  simpa using congrArg Subtype.val hx

/-! ## The MF radical -/

/-- **The printed MF radical.** `MFQuotientUnits.mfHomKernel G` is the
intersection of the kernels of all homomorphisms from `G` to MF groups. For
countable `G` it coincides with `manuscriptCoronaMFResidual G`. -/
theorem manuscriptSentence_mfRadicalDefinition :
    (∀ (G : Type) [Group G] (x : G),
      x ∈ MFQuotientUnits.mfHomKernel G ↔
        ∀ (M : Type) [Group M], IsOperatorMF M → ∀ f : G →* M, f x = 1) ∧
    ∀ (G : Type) [Group G] [Countable G],
      MFQuotientUnits.mfHomKernel G = manuscriptCoronaMFResidual G := by
  refine ⟨fun G _ x => MFQuotientUnits.mem_mfHomKernel_iff x, ?_⟩
  intro G _ _
  ext x
  refine (MFQuotientUnits.mem_mfHomKernel_iff x).trans ?_
  refine Iff.trans ?_ (NonMFSentences.manuscriptSentence_mfRadicalFormula G x).symm
  constructor
  · intro h M _ _ hM f
    exact h M ((isCDEOperatorMF_iff_isOperatorMF M).mp hM) f
  · intro h M _ hM f
    exact map_eq_one_of_isOperatorMF_of_killsCountableCDE h hM f

/-! ## The existence sentence -/

/-- **First clause.** `H = L_{𝔽₂}(1,2)^×` is nontrivial, and every
homomorphism from `H` to an MF group is trivial. -/
theorem manuscriptSentence_unitGroupKillsEveryMFHom :
    Nontrivial (UniversalLeavitt.BinaryLeavittAlgebra)ˣ ∧
      ∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ (f : (UniversalLeavitt.BinaryLeavittAlgebra)ˣ →* M)
          (x : (UniversalLeavitt.BinaryLeavittAlgebra)ˣ), f x = 1 := by
  obtain ⟨-, hFG, hnt, -, -, -, hkill, -⟩ :=
    OneSidedMFRadical.UnitGroupHeadline.manuscriptUnitGroupHeadline
  haveI : Countable (UniversalLeavitt.BinaryLeavittAlgebra)ˣ := countable_of_fg hFG
  refine ⟨hnt, ?_⟩
  intro M _ hM f x
  exact map_eq_one_of_isOperatorMF_of_killsCountableCDE (x := x)
    (fun M' _ _ hM' f' => hkill M' hM' f' x) hM f

/-- **Second clause.** The affine–Clifford witness `W` is sofic, and its central
sign `ε` is a nontrivial element killed by every homomorphism to an MF group. -/
theorem manuscriptSentence_soficWitnessWithMFInvisibleElement :
    IsSofic LiteralNonMFLinearWitness.WitnessGroup ∧
      CliffordWitnessHSRemark.witnessSign ≠ 1 ∧
      ∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ f : LiteralNonMFLinearWitness.WitnessGroup →* M,
          f CliffordWitnessHSRemark.witnessSign = 1 := by
  refine ⟨LiteralWitnessConsequences.witnessGroup_isSofic,
    CliffordWitnessHSRemark.witnessSign_ne_one, ?_⟩
  intro M _ hM f
  exact CliffordWitnessDirectDefect.map_sign_eq_one_of_isOperatorMF_target
    LiteralNonMFLinearWitness.alpha ExplicitLinearModel.conjD_injective
    ExplicitLinearModel.v1G_not_mem_range
    CommutingLampCollapse.gammaBar_hasKazhdanPropertyT hM f

/-- **The whole sentence.** "We construct groups for which every homomorphism to
an MF group is trivial, as well as a sofic group with a nontrivial element killed
by every MF homomorphism." -/
theorem manuscriptSentence_groupsWithNoMFImagesAndSoficWitness :
    (Nontrivial (UniversalLeavitt.BinaryLeavittAlgebra)ˣ ∧
      ∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ (f : (UniversalLeavitt.BinaryLeavittAlgebra)ˣ →* M)
          (x : (UniversalLeavitt.BinaryLeavittAlgebra)ˣ), f x = 1) ∧
    (IsSofic LiteralNonMFLinearWitness.WitnessGroup ∧
      CliffordWitnessHSRemark.witnessSign ≠ 1 ∧
      ∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ f : LiteralNonMFLinearWitness.WitnessGroup →* M,
          f CliffordWitnessHSRemark.witnessSign = 1) :=
  ⟨manuscriptSentence_unitGroupKillsEveryMFHom,
    manuscriptSentence_soficWitnessWithMFInvisibleElement⟩

/-! ## The OpenAI attribution -/

/-- **Mathematical content of the OpenAI attribution.** The unit group
`H = L_{𝔽₂}(1,2)^×` is not sofic. -/
theorem manuscriptSentence_openAINonsoficGroup :
    ¬ IsSofic (UniversalLeavitt.BinaryLeavittAlgebra)ˣ := by
  exact binaryLeavittUnits_not_isSofic (ZMod 2)

end AuditIntro
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms
  GroupApproximation.Manuscript.NonMF.AuditIntro.map_eq_one_of_isOperatorMF_of_killsCountableCDE
#audit_axioms
  GroupApproximation.Manuscript.NonMF.AuditIntro.manuscriptSentence_mfRadicalDefinition
#audit_axioms
  GroupApproximation.Manuscript.NonMF.AuditIntro.manuscriptSentence_unitGroupKillsEveryMFHom
#audit_axioms
  GroupApproximation.Manuscript.NonMF.AuditIntro.manuscriptSentence_soficWitnessWithMFInvisibleElement
#audit_axioms
  GroupApproximation.Manuscript.NonMF.AuditIntro.manuscriptSentence_groupsWithNoMFImagesAndSoficWitness
#audit_axioms
  GroupApproximation.Manuscript.NonMF.AuditIntro.manuscriptSentence_openAINonsoficGroup
