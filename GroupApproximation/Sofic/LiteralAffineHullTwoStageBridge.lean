import GroupApproximation.Sofic.FournierFacioHullBridge
import GroupApproximation.Sofic.LiteralAffineFreeProductBassSerreIndependence
import GroupApproximation.Sofic.LiteralAffineHullCommonQuotientInput
import GroupApproximation.Meta.AxiomGuard

/-!
# The specialized two-stage Hull boundary for the literal affine source

The absolute free-group avatar route is obstructed by every short source-kernel
word, and in particular by the doubled presentation's word `x xbar`.  Hull's
relative construction avoids that obstruction: the internal relations of the
source and Kazhdan partner live in free-product factors rather than becoming
long relators in an absolute free group.

This file records the smallest citation-faithful boundary for that route.  All
inputs *before* Hull are closed theorems:

* the whole free-product source is torsion-free and finitely presented;
* `Gamma(3)` is torsion-free, finitely presented, and Kazhdan;
* the amplified defect contains an explicit two-generated subgroup satisfying
  Hull's full suitability definition for the proved Bass--Serre action.

`TwoStageHull71Output` is the literal output required from the two applications
of Hull's Theorem 7.1.  It includes the common first quotient, the final
quotient, finite-order lifting, protected-set injectivity, and the two routing
statements.  The factor maps are required to come from the same first-stage
map; unrelated homomorphisms cannot inhabit the interface accidentally.

The nontrivial analytic statement still missing is exactly
`SpecializedHull71`: that this output is inhabited.  No declaration in this
file proves or assumes it, and no unconditional non-MF endpoint is stated.
Given an actual output, the rest of the file derives prescribed-subgroup
saturation, torsion-freeness, property `(T)`, protected survival, and the
existing `BareDefectHullQuotientData` entirely internally.
-/

namespace GroupApproximation
namespace LiteralAffineHullTwoStageBridge

open LiteralAffineFreeProductSource
open LiteralAffineFreeProductBassSerre
open LiteralAffineCongruenceSource
open HullSuitable

noncomputable section

/-- The certified Kazhdan factor in the common-quotient construction. -/
abbrev Partner : Type := CongruenceSubgroup.gamma3Partner.B

/-- The whole torsion-free source to which Hull's finite-order lifting clause
is applied. -/
abbrev Source : Type := LiteralAffineHullCommonQuotientInput.Source

/-- Inclusion of the amplified affine factor into the whole source. -/
def ambientInclusion : Ambient →* Source := Monoid.Coprod.inl

/-- Inclusion of the Kazhdan factor into the whole source. -/
def partnerInclusion : Partner →* Source := Monoid.Coprod.inr

/-! ## Closed inputs before Hull -/

/-- Every premise that is internal to the repository and precedes the two
applications of Hull's theorem. -/
def ConcretePreHullInputs : Prop :=
  IsPowerTorsionFree Source ∧
  Group.IsFinitelyPresented Source ∧
  IsPowerTorsionFree Partner ∧
  Group.IsFinitelyPresented Partner ∧
  HasKazhdanPropertyT.{0, 0} Partner ∧
  HullGeometry.IsSuitable 1 crossingSuitableCarrier
    (BassSerreFreeProduct.baseLeft Envelope :
      BassSerreHullGeometry.PathVertex Envelope)

/-- The full pre-Hull package is premise-free. -/
theorem concrete_preHull_inputs : ConcretePreHullInputs :=
  ⟨LiteralAffineHullCommonQuotientInput.source_isPowerTorsionFree,
    LiteralAffineHullCommonQuotientInput.source_isFinitelyPresented,
    CongruenceSubgroup.gamma3Partner.torsionFree,
    CongruenceSubgroup.gamma3Partner.finitelyPresented,
    CongruenceSubgroup.gamma3Partner.kazhdan,
    crossingSuitableCarrier_isSuitable⟩

#audit_closed_axioms concrete_preHull_inputs

/-! ## Exact output of the two applications -/

/-- The minimum coherent two-stage conclusion required from Hull 7.1.

The first application produces a common quotient, recorded by
`partnerSurjective`.  For the second application we carry the finite generating
tuple actually selected as Hull's target set and the pointwise conclusion
`secondRoutes`; saturation is derived below from those pointwise facts and the
surjectivity of the second quotient map.  It is not stored as a renamed Hull
conclusion.

The two `finiteOrderLifts` fields are Hull 7.1(e), once at each stage.  The two
`protected` fields are Hull 7.1(b), applied to the protected pair and then its
first-stage image. -/
structure TwoStageHull71Output where
  /-- The first common quotient. -/
  StageOne : Type
  [stageOneGroup : Group StageOne]
  /-- The final prescribed-saturation quotient. -/
  Final : Type
  [finalGroup : Group Final]
  [finalCountable : Countable Final]
  /-- The single first-stage map from the whole free product. -/
  whole : Source →* StageOne
  /-- Its restriction to the Kazhdan factor. -/
  partner : Partner →* StageOne
  /-- Its restriction to the amplified affine factor. -/
  ambient : Ambient →* StageOne
  /-- Coherence on the Kazhdan factor. -/
  whole_partner : whole.comp partnerInclusion = partner
  /-- Coherence on the amplified affine factor. -/
  whole_ambient : whole.comp ambientInclusion = ambient
  /-- The first stage is already a common quotient on the Kazhdan side. -/
  partnerSurjective : Function.Surjective partner
  /-- Hull 7.1(e) at the first stage, read from the whole torsion-free source. -/
  firstFiniteOrderLifts :
    ∀ (y : StageOne) (n : ℕ), 0 < n → orderOf y = n →
      ∃ x : Source, orderOf x = n ∧ whole x = y
  /-- Hull 7.1(b) protects `1` and the marked source element at stage one. -/
  firstProtected : Set.InjOn ambient
    ({1, amplifiedDefectData.s} : Set Ambient)
  /-- A finite generating tuple chosen as the target set for stage two. -/
  stageOneCard : ℕ
  /-- The chosen generators of the first quotient. -/
  stageOneGen : Fin stageOneCard → StageOne
  /-- The chosen tuple genuinely generates the first quotient. -/
  stageOneGenerates : Subgroup.closure (Set.range stageOneGen) = ⊤
  /-- The second quotient map. -/
  finish : StageOne →* Final
  /-- Hull's quotient map at the second stage. -/
  finishSurjective : Function.Surjective finish
  /-- Hull 7.1(c), one chosen target at a time. -/
  secondRoutes : ∀ j : Fin stageOneCard,
    finish (stageOneGen j) ∈
      crossingSuitableCarrier.map (finish.comp ambient)
  /-- Hull 7.1(e) at the second stage. -/
  secondFiniteOrderLifts :
    ∀ (z : Final) (n : ℕ), 0 < n → orderOf z = n →
      ∃ y : StageOne, orderOf y = n ∧ finish y = z
  /-- Hull 7.1(b) protects the image of the protected pair at stage two. -/
  secondProtected : Set.InjOn finish
    (ambient '' ({1, amplifiedDefectData.s} : Set Ambient))

/-- The exact remaining analytic theorem.  This is a proposition, not an
axiom or an input to any unconditional endpoint in this module. -/
def SpecializedHull71 : Prop := Nonempty TwoStageHull71Output

namespace TwoStageHull71Output

variable (H : TwoStageHull71Output)

local instance : Group H.StageOne := H.stageOneGroup
local instance : Group H.Final := H.finalGroup
local instance : Countable H.Final := H.finalCountable

/-- The pointwise routing clause extends from the chosen generators to the
entire image of the second quotient map. -/
theorem finish_range_le_suitable_map :
    H.finish.range ≤
      crossingSuitableCarrier.map (H.finish.comp H.ambient) := by
  have hle : Subgroup.closure (Set.range H.stageOneGen) ≤
      (crossingSuitableCarrier.map (H.finish.comp H.ambient)).comap H.finish := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact H.secondRoutes j
  intro z hz
  obtain ⟨y, rfl⟩ := hz
  have hy : y ∈ Subgroup.closure (Set.range H.stageOneGen) := by
    rw [H.stageOneGenerates]
    exact Subgroup.mem_top y
  exact hle hy

/-- The suitable two-generated carrier fills the final quotient.  This is the
purely algebraic content of the two prescribed-target clauses. -/
theorem suitable_map_eq_top :
    crossingSuitableCarrier.map (H.finish.comp H.ambient) = ⊤ := by
  apply top_unique
  rw [← MonoidHom.range_eq_top.mpr H.finishSurjective]
  exact H.finish_range_le_suitable_map

/-- The Kazhdan factor still fills the final quotient.  This is derived by
composition of the two quotient maps, not carried as a separate Hull field. -/
theorem finalPartnerSurjective :
    Function.Surjective (H.finish.comp H.partner) :=
  H.finishSurjective.comp H.partnerSurjective

/-- Since the suitable carrier lies in the compression defect, the entire
defect fills the final quotient. -/
theorem defect_map_eq_top :
    amplifiedDefectData.core.defectNormal.map
      (H.finish.comp H.ambient) = ⊤ :=
  crossingSuitableDefectSubgroup.defect_map_eq_top H.suitable_map_eq_top

/-- The two finite-order lifting clauses compose. -/
theorem finiteOrder_lifts :
    ∀ (z : H.Final) (n : ℕ), 0 < n → orderOf z = n →
      ∃ x : Source, orderOf x = n ∧
        (H.finish.comp H.whole) x = z := by
  intro z n hn hz
  obtain ⟨y, hyOrder, hy⟩ := H.secondFiniteOrderLifts z n hn hz
  obtain ⟨x, hxOrder, hx⟩ := H.firstFiniteOrderLifts y n hn hyOrder
  exact ⟨x, hxOrder, by simp only [MonoidHom.comp_apply, hx, hy]⟩

/-- The protected-pair injections compose. -/
theorem protected_injective :
    Set.InjOn (H.finish.comp H.ambient)
      ({1, amplifiedDefectData.s} : Set Ambient) :=
  HullPrescribedSaturation.injOn_comp H.ambient H.finish
    ({1, amplifiedDefectData.s} : Set Ambient)
      H.firstProtected H.secondProtected

/-- The final target is torsion-free, derived from the whole source and the
composed finite-order lifting clause. -/
theorem final_torsionFree : IsPowerTorsionFree H.Final :=
  isPowerTorsionFree_of_orderReflecting
    LiteralAffineHullCommonQuotientInput.source_isPowerTorsionFree
    (H.finish.comp H.whole) H.finiteOrder_lifts

/-- Property `(T)` descends from the certified partner along the second-stage
surjection. -/
theorem final_kazhdan : HasKazhdanPropertyT.{0, 0} H.Final :=
  HasKazhdanPropertyT.of_surjective (H.finish.comp H.partner)
    H.finalPartnerSurjective CongruenceSubgroup.gamma3Partner.kazhdan

/-- All remaining algebra lands in the existing bare Hull endpoint bundle.
This is deliberately a constructor from an actual Hull output, not a theorem
that such an output exists. -/
def toBareDefectHullQuotientData :
    BareDefectHullQuotientData amplifiedDefectData := by
  have hsaturation :
      (amplifiedDefectData.core.defectNormal.map H.ambient).map H.finish = ⊤ := by
    rw [Subgroup.map_map]
    exact H.defect_map_eq_top
  exact BareDefectHullQuotientData.ofCommonQuotientAndHull
    H.partner H.whole H.ambient H.finish H.partnerSurjective
    LiteralAffineHullCommonQuotientInput.source_isPowerTorsionFree
    CongruenceSubgroup.gamma3Partner.kazhdan hsaturation
    H.firstFiniteOrderLifts H.secondFiniteOrderLifts
    H.firstProtected H.secondProtected

end TwoStageHull71Output

end

end LiteralAffineHullTwoStageBridge
end GroupApproximation
