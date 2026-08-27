import GroupApproximation.Higman.OmegaFatShearedLinkBase
import GroupApproximation.Higman.ExplicitFreeEdge

/-!
# One asymmetric coordinate edge for the sheared Omega link

For `j + 1 ≤ m`, the source alphabet is the `j`-coordinate window and the
target alphabet is obtained by increasing coordinate `j` by one.  Both are
evaluated in the final width-`m` sheared semantic base.  This is the literal
free-edge datum which a matched finite cutter must compress at the successor
step.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Seq

theorem blockSet_mono {j m : ℕ} (hjm : j ≤ m) :
    blockSet j ⊆ blockSet m := by
  intro beta hbeta i hi
  apply hbeta i
  intro hij
  apply hi
  have hbounds := Finset.mem_Ico.mp hij
  exact Finset.mem_Ico.mpr
    ⟨hbounds.1, lt_of_lt_of_le hbounds.2 (by exact_mod_cast hjm)⟩

/-- Include a smaller block alphabet into a larger one. -/
def shearedBlockIncl {j m : ℕ} (hjm : j ≤ m) :
    ↥(blockSet j) → ↥(blockSet m) :=
  fun beta => ⟨beta.1, blockSet_mono hjm beta.2⟩

theorem shearedBlockIncl_injective {j m : ℕ} (hjm : j ≤ m) :
    Function.Injective (shearedBlockIncl hjm) := by
  intro beta gamma h
  exact Subtype.ext (congrArg Subtype.val h)

/-- Increase the first coordinate outside the source window. -/
noncomputable def shearedBlockStep (j : ℕ) :
    ↥(blockSet j) → ↥(blockSet (j + 1)) :=
  fun beta =>
    ⟨beta.1 + Finsupp.single (j : ℤ) 1,
      add_single_mem_blockSet
        (blockSet_mono (Nat.le_succ j) beta.2) 1⟩

theorem shearedBlockStep_injective (j : ℕ) :
    Function.Injective (shearedBlockStep j) := by
  intro beta gamma h
  apply Subtype.ext
  have hv := congrArg Subtype.val h
  exact add_right_cancel hv

/-- Source evaluation for the `j`th coordinate edge inside final width `m`. -/
noncomputable def fatShearedCoordinateSource
    (m j : ℕ) (hjm : j ≤ m) :
    FreeGroup ↥(blockSet j) →* FatCent3 m × F₃ :=
  (fatShearedLinkLift m).comp (FreeGroup.map (shearedBlockIncl hjm))

/-- Target evaluation after increasing coordinate `j` by one. -/
noncomputable def fatShearedCoordinateTarget
  (m j : ℕ) (hjm : j + 1 ≤ m) :
    FreeGroup ↥(blockSet j) →* FatCent3 m × F₃ :=
  (fatShearedLinkLift m).comp
    (FreeGroup.map
      (fun beta => shearedBlockIncl hjm (shearedBlockStep j beta)))

theorem fatShearedCoordinateSource_injective
    (m j : ℕ) (hjm : j ≤ m) :
    Function.Injective (fatShearedCoordinateSource m j hjm) :=
  (fatShearedLinkLift_injective m).comp
    (FreeGroup.map_injective (shearedBlockIncl_injective hjm))

theorem fatShearedCoordinateTarget_injective
    (m j : ℕ) (hjm : j + 1 ≤ m) :
    Function.Injective (fatShearedCoordinateTarget m j hjm) :=
  (fatShearedLinkLift_injective m).comp
    (FreeGroup.map_injective
      ((shearedBlockIncl_injective hjm).comp
        (shearedBlockStep_injective j)))

@[simp] theorem fatShearedCoordinateSource_of
    (m j : ℕ) (hjm : j ≤ m) (beta : ↥(blockSet j)) :
    fatShearedCoordinateSource m j hjm (FreeGroup.of beta) =
      slimFatSemanticBaseEmb m (slimLinkElem m beta.1) := by
  simp [fatShearedCoordinateSource, fatShearedLinkLift, shearedBlockIncl,
    slimLinkLift]

@[simp] theorem fatShearedCoordinateTarget_of
    (m j : ℕ) (hjm : j + 1 ≤ m) (beta : ↥(blockSet j)) :
    fatShearedCoordinateTarget m j hjm (FreeGroup.of beta) =
      slimFatSemanticBaseEmb m
        (slimLinkElem m
          (beta.1 + Finsupp.single (j : ℤ) 1)) := by
  simp [fatShearedCoordinateTarget, fatShearedLinkLift, shearedBlockIncl,
    shearedBlockStep, slimLinkLift]

/-- The honest asymmetric HNN correspondence for adjoining coordinate `j`. -/
noncomputable def fatShearedCoordinateEdge
    (m j : ℕ) (hjm : j + 1 ≤ m) :
    ExplicitFreeEdge.Data ↥(blockSet j) (FatCent3 m × F₃) where
  source := fatShearedCoordinateSource m j (le_trans (Nat.le_succ j) hjm)
  target := fatShearedCoordinateTarget m j hjm
  source_injective := fatShearedCoordinateSource_injective m j _
  target_injective := fatShearedCoordinateTarget_injective m j hjm

theorem fatShearedCoordinateEdge_stable_conj
    (m j : ℕ) (hjm : j + 1 ≤ m) (beta : ↥(blockSet j)) :
    (HNNExtension.t :
        ExplicitFreeEdge.Extension (fatShearedCoordinateEdge m j hjm)) *
        HNNExtension.of
          (slimFatSemanticBaseEmb m (slimLinkElem m beta.1)) *
        HNNExtension.t⁻¹ =
      HNNExtension.of
        (slimFatSemanticBaseEmb m
          (slimLinkElem m
            (beta.1 + Finsupp.single (j : ℤ) 1))) := by
  simpa only [fatShearedCoordinateEdge,
    fatShearedCoordinateSource_of, fatShearedCoordinateTarget_of]
    using ExplicitFreeEdge.stable_conj_source
      (fatShearedCoordinateEdge m j hjm) (FreeGroup.of beta)

end Omega
end Higman
end GroupApproximation
