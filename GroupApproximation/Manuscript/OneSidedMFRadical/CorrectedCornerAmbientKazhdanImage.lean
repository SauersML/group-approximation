import GroupApproximation.Manuscript.OneSidedMFRadical.RetainedCoronaHom
import GroupApproximation.Manuscript.OneSidedMFRadical.CorrectedCornerProvenanceData

/-!
# The ambient image of the subgroup Kazhdan projection

For provenance-rich corrected-corner data, this file bundles the restriction
of the original corona representation to the normal Kazhdan subgroup, its
maximal-group-C-star lift, and their retained-coordinate omega versions.  The
retained integrated map sends the maximal Kazhdan projection to the retained
ambient fixed-space projection `p`, equivalently to `1 - q`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter
open AbstractSpectralGap MaximalCStarKazhdanProjection
open PrintedCornerCompression UltraproductKazhdanProjection

noncomputable section

variable {G : Type} [Group G] [Countable G]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
variable (K : Subgroup G)

/-- The original ambient corona representation restricted to the Kazhdan
subgroup. -/
def provenanceAmbientSubgroupRepresentation
    (P : CorrectedCornerProvenanceData G X K) :
    K →* unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
  P.rho.comp K.subtype

/-- Its integrated maximal-group-C-star map in the original ambient corona. -/
noncomputable def provenanceAmbientSubgroupLift
    (P : CorrectedCornerProvenanceData G X K) :
    MaximalGroupCStar K →⋆ₐ[ℂ]
      NormMatrixCStarCorona (fun n ↦ X n) :=
  (maximalGroupCStar_existsUnique_lift_allUniverses K
    (provenanceAmbientSubgroupRepresentation K P)).choose

/-- Exact generator equation for the original ambient lift. -/
@[simp] theorem provenanceAmbientSubgroupLift_generator
    (P : CorrectedCornerProvenanceData G X K) (k : K) :
    provenanceAmbientSubgroupLift K P
        (maximalGroupCStarGenerator K k) =
      ((provenanceAmbientSubgroupRepresentation K P k :
        unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) :=
  (maximalGroupCStar_existsUnique_lift_allUniverses K
    (provenanceAmbientSubgroupRepresentation K P)).choose_spec.1 k

/-- Before discarding coordinates, the integrated subgroup representation
sends the maximal Kazhdan projection to the provenance projection `P.p`. -/
theorem provenanceAmbientSubgroupLift_kazhdanProjection
    (P : CorrectedCornerProvenanceData G X K) :
    provenanceAmbientSubgroupLift K P P.kazhdan.projection = P.p := by
  let C := normalSubgroupKazhdanCompressionData P.rho K P.kazhdan
  have himage : provenanceAmbientSubgroupLift K P P.kazhdan.projection =
      C.proj := by
    exact image_eq_spectralProjection P.kazhdan
      (provenanceAmbientSubgroupRepresentation K P)
      (provenanceAmbientSubgroupLift K P)
      (provenanceAmbientSubgroupLift_generator K P) C.kt_07_kazhdan_gap
  exact himage.trans P.p_eq.symm

/-- The ambient algebra after coordinate retention and passage to the chosen
refining ultrafilter. -/
abbrev ProvenanceRetainedAmbientCorona
    (P : CorrectedCornerProvenanceData G X K) (ω : Ultrafilter ℕ) :=
  FilterMatrixCStarCorona (fun n ↦ X (P.phi n)) (ω : Filter ℕ)

/-- Restrict the original ambient subgroup representation to the retained
coordinates and then pass to the omega corona. -/
noncomputable def provenanceRetainedAmbientSubgroupRepresentation
    (P : CorrectedCornerProvenanceData G X K)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) :
    K →* unitary (ProvenanceRetainedAmbientCorona K P ω) :=
  (unitaryMap (retainedCoronaToOmega X P.phi P.phi_strictMono ω hω)).comp
    (provenanceAmbientSubgroupRepresentation K P)

/-- The retained integrated map, defined as the retained-coordinate star map
composed with the original integrated map. -/
noncomputable def provenanceRetainedAmbientSubgroupLift
    (P : CorrectedCornerProvenanceData G X K)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) :
    MaximalGroupCStar K →⋆ₐ[ℂ]
      ProvenanceRetainedAmbientCorona K P ω :=
  (retainedCoronaToOmega X P.phi P.phi_strictMono ω hω).comp
    (provenanceAmbientSubgroupLift K P)

/-- Exact generator equation needed for maximal-C-star uniqueness after
coordinate retention. -/
@[simp] theorem provenanceRetainedAmbientSubgroupLift_generator
    (P : CorrectedCornerProvenanceData G X K)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) (k : K) :
    provenanceRetainedAmbientSubgroupLift K P ω hω
        (maximalGroupCStarGenerator K k) =
      ((provenanceRetainedAmbientSubgroupRepresentation K P ω hω k :
        unitary (ProvenanceRetainedAmbientCorona K P ω)) :
          ProvenanceRetainedAmbientCorona K P ω) := by
  rw [provenanceRetainedAmbientSubgroupLift, StarAlgHom.comp_apply,
    provenanceAmbientSubgroupLift_generator]
  rfl

/-- The retained integrated map sends the maximal Kazhdan projection to the
retained image of the ambient fixed-space projection. -/
theorem provenanceRetainedAmbientSubgroupLift_kazhdanProjection
    (P : CorrectedCornerProvenanceData G X K)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) :
    provenanceRetainedAmbientSubgroupLift K P ω hω
        P.kazhdan.projection =
      retainedCoronaToOmega X P.phi P.phi_strictMono ω hω P.p := by
  rw [provenanceRetainedAmbientSubgroupLift, StarAlgHom.comp_apply,
    provenanceAmbientSubgroupLift_kazhdanProjection]

/-- Equivalent complement formula: the same image is one minus the retained
corner projection.  This is the exact value used in complement-unitization;
it is generally not zero. -/
theorem provenanceRetainedAmbientSubgroupLift_kazhdanProjection_eq_one_sub_q
    (P : CorrectedCornerProvenanceData G X K)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) :
    provenanceRetainedAmbientSubgroupLift K P ω hω
        P.kazhdan.projection =
      1 - retainedCoronaToOmega X P.phi P.phi_strictMono ω hω P.q := by
  rw [provenanceRetainedAmbientSubgroupLift_kazhdanProjection,
    P.q_eq, map_sub, map_one]
  abel

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
