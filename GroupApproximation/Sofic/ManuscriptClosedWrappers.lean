import GroupApproximation.Analysis.ProperIsometryFromCompression
import GroupApproximation.Computability.MarkovMFConsequences
import GroupApproximation.Sofic.CommutingLampCollapse
import GroupApproximation.Sofic.IntertwinerKazhdanTransport
import GroupApproximation.Sofic.MFRelationClosure
import GroupApproximation.Sofic.MarkedMFClosed
import GroupApproximation.Sofic.MatricialStabilityRadical
import GroupApproximation.Sofic.ProjectionCompressionCollapse
import GroupApproximation.Sofic.ScaledKazhdanTransport
import GroupApproximation.Sofic.TorsionSpectralCollapse
import GroupApproximation.Sofic.NormTraceGap
import GroupApproximation.Sofic.WeakMFVectorGNS

/-!
# Closed forms of the parameterized manuscript badges — SUPERSEDED

**Do not point a manuscript badge at anything in this file.**

Every theorem here is a zero-input restatement of an endpoint that was
parameterized when this module was written (38764495).  That premise no
longer holds: the six "Zero-input badges" commits of 2026-08-16
rewrote the *originals* into closed `∀`-form in place, keeping their
universe polymorphism. Every remaining declaration wrapped
here is therefore already closed, already cited by the manuscript, and
already more general than its wrapper.

More general, specifically. Several wrappers quantify
over `Type` where the original quantifies over `Type u` or `Type*`, and
`manuscriptMFRecognitionUndecidable` collapses two independent
universes into one.  Each wrapper is proved by `exact <original> …`,
which certifies only that the wrapper *follows* from the original --- a
strictly weaker restatement compiles exactly as happily.  So a badge
moved onto one of these would silently certify less than the sentence
above it in the manuscript: `manuscriptProperCompressionTraceless`
covers only `Type 0` C*-algebras, while the printed claim, and
`no_faithfulTracialState` itself, cover every C*-algebra in every
universe.

This layer is kept only so the supersession is on the record rather
than rediscovered.  Nothing cites it.  Retiring it is the clean end
state; a second hand-maintained copy of these propositions has already
drifted from its originals once.
-/

namespace GroupApproximation
namespace ManuscriptClosedWrappers

open MarkedCompression CommutingLampCollapse Matrix
open scoped commutatorElement

noncomputable section

/-- Quotients of countable groups are countable; mirrored locally from
`Sofic.TorsionSpectralCollapse`, where the same instance is `local`. -/
local instance quotientCountable {E : Type} [Group E] (N : Subgroup E)
    [hN : N.Normal] [Countable E] : Countable (E ⧸ N) :=
  Function.Surjective.countable
    (@QuotientGroup.mk'_surjective E _ N hN)

/-! ## Proper compression in a unital algebra -/

/-- Closed form: the isometry of a proper projection compression is not a
unit. -/
theorem manuscriptProperIsometryNotUnit :
    ∀ {A : Type} [Ring A] [StarRing A]
      (D : ProperProjectionCompression A),
      ¬ IsUnit D.isometry := by
  intro A _ _ D
  exact D.isometry_not_isUnit

/-- Closed form: a proper projection compression forbids stable
finiteness. -/
theorem manuscriptProperCompressionNotStablyFinite :
    ∀ {A : Type} [Ring A] [StarRing A]
      (_D : ProperProjectionCompression A),
      ¬ IsStablyFiniteRing A := by
  intro A _ _ D
  exact D.not_isStablyFiniteRing

/-- Closed form: a proper projection compression forbids a faithful
tracial state. -/
theorem manuscriptProperCompressionTraceless :
    ∀ {B : Type} [CStarAlgebra B]
      (_D : ProperProjectionCompression B),
      ¬ Nonempty (FaithfulTracialState B) := by
  intro B _ D
  exact D.no_faithfulTracialState

/-! ## Undecidability -/

/-- Closed form: MF recognition is undecidable given any computable
Adian--Rabin reduction from an undecidable source. -/
theorem manuscriptMFRecognitionUndecidable :
    ∀ {Source Code : Type} [Primcodable Source] [Primcodable Code]
      (sourceProperty : Source → Prop)
      (semantics : MarkovMFConsequences.FinitePresentationSemantics Code)
      (_ : MarkovMFConsequences.AdianRabinReduction sourceProperty
        (MarkovMFConsequences.operatorMFProperty semantics)),
      ¬ ComputablePred sourceProperty →
      ¬ ComputablePred (MarkovMFConsequences.operatorMFProperty semantics) := by
  intro Source Code _ _ sourceProperty semantics reduction hsource
  exact MarkovMFConsequences.recognition_undecidable reduction hsource

/-- Closed form: operator MF passes to subgroups. -/
theorem manuscriptSubgroupHereditary :
    ∀ {G : Type} [Group G], IsOperatorMF G →
      ∀ H : Subgroup G, IsOperatorMF H := by
  intro G _ hG H
  exact MarkovMFConsequences.operatorMF_subgroup_hereditary hG H

/-! ## The commuting-lamp quotient -/

/-- Closed form of the commuting-lamp collapse: killing the central sign
puts the moved-lamp commutator inside the MF radical of the quotient,
nontrivially. -/
theorem manuscriptCommutingLampCollapse :
    ∀ {Γ : Type} [Group Γ] (α : Γ →* Γ)
      (hα : Function.Injective α)
      [Countable (Ambient α hα)],
      HasKazhdanPropertyT.{0, 0} Γ →
      ∀ a₀ : Γ, a₀ ∉ Set.range α →
      (⁅(QuotientGroup.mk' (Subgroup.zpowers (signAmbient α hα)))
          (iotaAmbient α hα a₀),
        (QuotientGroup.mk' (Subgroup.zpowers (signAmbient α hα)))
          (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹)⁆ ∈
        actualCoronaMFResidual
          (Ambient α hα ⧸ Subgroup.zpowers (signAmbient α hα))) ∧
      ⁅(QuotientGroup.mk' (Subgroup.zpowers (signAmbient α hα)))
          (iotaAmbient α hα a₀),
        (QuotientGroup.mk' (Subgroup.zpowers (signAmbient α hα)))
          (tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹)⁆ ≠ 1 ∧
      ¬ IsCDEOperatorMF
        (Ambient α hα ⧸ Subgroup.zpowers (signAmbient α hα)) := by
  intro Γ _ α hα _ hT a₀ ha₀
  exact CommutingLampCollapse.commutingLampQuotient_collapse α hα hT ha₀

/-! ## Scaled transport -/

/-- Closed form of the two-sided scaled transport. -/
theorem manuscriptScaledTransportBoth :
    ∀ {Γ E : Type} [Group Γ] [Group E]
      (B : OpAlmostRepresentation E) (w : ℕ → ℝ),
      (∀ n, 0 ≤ w n) →
      ∀ (C : KazhdanCompressionCore Γ E)
        (x : ∀ n, Matrix (B.model n) (B.model n) ℂ),
      ScaledKazhdanTransport.IsScaledAsymptoticCommutant B w C x →
      ScaledKazhdanTransport.IsScaledMassBounded B w x →
      ScaledKazhdanTransport.IsScaledAsymptoticCommutant B w C (fun n ↦
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
            (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) ∧
        ScaledKazhdanTransport.IsScaledAsymptoticCommutant B w C (fun n ↦
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
            (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) := by
  intro Γ E _ _ B w hw C x hx hbound
  exact ScaledKazhdanTransport.scaled_transport_both B w hw C x hx hbound

/-- Closed form of the rectangular scaled intertwiner transport. -/
theorem manuscriptScaledIntertwinerTransport :
    ∀ {Γ E : Type} [Group Γ] [Group E]
      (B₁ B₂ : OpAlmostRepresentation E) (w : ℕ → ℝ),
      (∀ n, 0 ≤ w n) →
      ∀ (C : KazhdanCompressionCore Γ E)
        (x : ∀ n, Matrix (B₁.model n) (B₂.model n) ℂ),
      IntertwinerKazhdanTransport.IsScaledAsymptoticIntertwinerOf
        B₁ B₂ w C.iota x →
      IntertwinerKazhdanTransport.IsScaledRectMassBounded B₁ B₂ w x →
      IntertwinerKazhdanTransport.IsScaledAsymptoticIntertwinerOf
        B₁ B₂ w C.iota (fun n ↦
          (B₁.map n C.t : Matrix (B₁.model n) (B₁.model n) ℂ) * x n *
            (B₂.map n C.t : Matrix (B₂.model n) (B₂.model n) ℂ)ᴴ) := by
  intro Γ E _ _ B₁ B₂ w hw C x hx hbound
  exact IntertwinerKazhdanTransport.scaled_intertwiner_transport B₁ B₂ w hw
    C x hx hbound

/-! ## The relation closure -/

/-- Closed form of the membership characterization of the corona relation
closure. -/
theorem manuscriptRelationClosureMembership :
    ∀ {G : Type} [Group G] (N : Subgroup G) [N.Normal] (x : G),
      x ∈ actualCoronaMFClosure N ↔
        ∀ (X : ℕ → FiniteModel), ∀ hX : ∀ n, 0 < Fintype.card (X n),
          letI : ∀ n, Nonempty (X n) :=
            fun n ↦ Fintype.card_pos_iff.mp (hX n)
          ∀ rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
            (∀ y ∈ N, rho y = 1) → rho x = 1 := by
  intro G _ N _ x
  exact mem_actualCoronaMFClosure_iff

/-! ## Marked certificates -/

/-- Closed form: a non-MF marked group has a word-ball certificate whose
cylinder avoids the MF locus. -/
theorem manuscriptMarkedBallCertificate :
    ∀ (k : ℕ) (M : MarkedGroupSpace k),
      ¬ IsOperatorMF M.Quotient →
      ∃ R : ℕ,
        MarkedGroupSpace.cylinder M (MarkedGroupSpace.wordBall k R) ⊆
          (MarkedGroupSpace.operatorMFLocus k)ᶜ := by
  intro k M hM
  exact MarkedGroupSpace.exists_wordBall_cylinder_subset_compl_operatorMFLocus
    M hM

/-! ## Matricial stability -/

/-- Closed form: for point-norm matricially stable groups the corona
residual is the finite-dimensional unitary residual. -/
theorem manuscriptStabilityRadicalIdentification :
    ∀ {G : Type} [Group G] [Countable G],
      MatricialStabilityRadical.IsPointNormMatriciallyStable G →
      actualCoronaMFResidual G =
        MatricialStabilityRadical.fdUnitaryResidual G := by
  intro G _ _ hstab
  exact MatricialStabilityRadical.actualCoronaMFResidual_eq_fdUnitaryResidual
    hstab

/-- Closed form: a stable group with nontrivial finite-dimensional
residual is not MF. -/
theorem manuscriptStabilityNonMFCriterion :
    ∀ {G : Type} [Group G] [Countable G],
      MatricialStabilityRadical.IsPointNormMatriciallyStable G →
      MatricialStabilityRadical.fdUnitaryResidual G ≠ ⊥ →
      ¬ IsCDEOperatorMF G := by
  intro G _ _ hstab hne
  exact MatricialStabilityRadical.not_isCDEOperatorMF_of_stable_of_fdResidual_ne_bot
    hstab hne

/-! ## Projection and torsion collapse -/

/-- Closed form of the corona projection collapse. -/
theorem manuscriptProjectionCollapse :
    ∀ {E : Type} [Group E] [Countable E]
      (L : Subgroup E), HasKazhdanPropertyT.{0, 0} L →
      ∀ s : E, (∀ γ ∈ L, s * γ * s⁻¹ ∈ L) →
      ∀ (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)),
      letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
      ∀ (pi : E →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
        (p : NormMatrixCStarCorona (fun n ↦ X n)),
        star p = p → p * p = p →
        (∀ γ ∈ L,
          ((pi (s * γ * s⁻¹) :
              unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
              NormMatrixCStarCorona (fun n ↦ X n)) * p =
            p * ((pi (s * γ * s⁻¹) :
                unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
              NormMatrixCStarCorona (fun n ↦ X n))) →
        (∀ γ₁ ∈ L, ∀ γ₂ ∈ L,
          Commute
            (((pi γ₁ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
                NormMatrixCStarCorona (fun n ↦ X n)) * p *
              star ((pi γ₁ :
                  unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
                NormMatrixCStarCorona (fun n ↦ X n)))
            (((pi γ₂ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
                NormMatrixCStarCorona (fun n ↦ X n)) * p *
              star ((pi γ₂ :
                  unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
                NormMatrixCStarCorona (fun n ↦ X n)))) →
        ∀ γ ∈ L,
          ((pi γ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
              NormMatrixCStarCorona (fun n ↦ X n)) * p =
            p * ((pi γ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
              NormMatrixCStarCorona (fun n ↦ X n)) := by
  intro E _ _ L hT s hcomp X hX
  exact ProjectionCompressionCollapse.corona_projection_collapse L hT
    (s := s) hcomp X hX

/-- Closed form: torsion witnesses have invisible commutators. -/
theorem manuscriptTorsionWitnessInvisible :
    ∀ {E : Type} [Group E] [Countable E]
      (L : Subgroup E), HasKazhdanPropertyT.{0, 0} L →
      ∀ s : E, (∀ γ ∈ L, s * γ * s⁻¹ ∈ L) →
      ∀ k : E,
        TorsionCompressionCollapse.IsTorsionCompressionWitness L s k →
      ∀ γ ∈ L, ActualCoronaMFInvisible ⁅γ, k⁆ := by
  intro E _ _ L hT s hcomp k hk γ hγ
  exact TorsionSpectralCollapse.actualCoronaMFInvisible_of_torsionWitness
    hT hcomp hk hγ

/-- Closed form: the torsion collapse defect sits inside the corona
residual. -/
theorem manuscriptTorsionDefectInRadical :
    ∀ {E : Type} [Group E] [Countable E]
      (L : Subgroup E), HasKazhdanPropertyT.{0, 0} L →
      ∀ s : E, (∀ γ ∈ L, s * γ * s⁻¹ ∈ L) →
      TorsionCompressionCollapse.torsionCollapseDefect L s ≤
        actualCoronaMFResidual E := by
  intro E _ _ L hT s hcomp
  exact TorsionSpectralCollapse.torsionCollapseDefect_le_actualCoronaMFResidual_of_kazhdan
    hT hcomp

/-- Closed form: an MF quotient by the torsion collapse defect pins the
residual exactly. -/
theorem manuscriptTorsionDefectIsRadical :
    ∀ {E : Type} [Group E] [Countable E]
      (L : Subgroup E), HasKazhdanPropertyT.{0, 0} L →
      ∀ s : E, (∀ γ ∈ L, s * γ * s⁻¹ ∈ L) →
      IsCDEOperatorMF
        (E ⧸ TorsionCompressionCollapse.torsionCollapseDefect L s) →
      actualCoronaMFResidual E =
        TorsionCompressionCollapse.torsionCollapseDefect L s := by
  intro E _ _ L hT s hcomp hquot
  exact TorsionSpectralCollapse.actualCoronaMFResidual_eq_torsionCollapseDefect_of_kazhdan
    hT hcomp hquot

/-! ## Norm models and the spectral gap -/

/-- Closed form: every norm model pads to one with all pairwise
Hilbert--Schmidt distances below any prescribed bound. -/
theorem manuscriptNormModelHSCollapse :
    ∀ {G : Type} [Group G] (F : Finset G) (δ ε : ℝ)
      (_M : NormModel G F δ ε) (η : ℝ), 0 < η →
      ∃ M' : NormModel G F δ ε,
        ∀ g ∈ F, ∀ h ∈ F,
          hsDistSq M'.carrier (M'.map g) (M'.map h) ≤ η := by
  intro G _ F δ ε M η hη
  exact M.exists_hs_collapse hη

/-- Closed form of the robust spectral gap: past a threshold stage no
eigenvalue of the Hermitian generator average is intermediate. -/
theorem manuscriptRobustSpectralGap :
    ∀ {G : Type} [Group G] (Q : Finset G) (ε : ℝ),
      IsKazhdanPair.{0, 0} G Q ε →
      ∀ S : Finset G, Q ⊆ S → 1 ∈ S → ε ≤ 1 →
      (∀ g ∈ S, g⁻¹ ∈ S) →
      ∀ (A : OpAlmostRepresentation G) (a b : ℝ),
        1 - ε ^ 2 / (4 * S.card) < a → b < 1 →
        ∃ N : ℕ, ∀ n ≥ N, ∀ i : A.model n,
          ¬ (a ≤ Matrix.IsHermitian.eigenvalues
              (KazhdanCornerMatrices.hermitianAverage_conjTranspose A S n) i ∧
            Matrix.IsHermitian.eigenvalues
              (KazhdanCornerMatrices.hermitianAverage_conjTranspose A S n) i ≤ b) := by
  intro G _ Q ε hQ S hQS hone hεone hsymm A a b ha hb
  exact WeakMFVectorGNS.hermitianAverage_eventually_no_intermediate_eigenvalues
    hQ S hQS hone hεone hsymm A ha hb

end

end ManuscriptClosedWrappers
end GroupApproximation
