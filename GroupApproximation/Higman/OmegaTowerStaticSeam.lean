import GroupApproximation.Higman.OmegaTowerStableHullIteration

/-!
# The single static seam left in the Omega descent

The desired `F₃` intersection is already stable under the outer edge and is
contained in the stable hull by the constructive half of Mikaelian's block
argument.  Consequently the entire outer scan reduces to one intersection in
the stage-two base: adjoining the desired range subgroup to `slimWBase` must
not create any further element of the embedded `F₃`.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- The desired Omega subgroup, embedded in the stage-two base. -/
noncomputable def omegaRangeSub (m : ℕ) (B : Set E) : Subgroup (SlimPi m) :=
  (ASub (omegaOp m B)).map (slimPiF3Hom m)

/-- The sole remaining static normal-form seam. -/
def StaticSeam (m : ℕ) (B : Set E) : Prop :=
  (slimWBase m B ⊔ omegaRangeSub m B) ⊓ (slimPiF3Hom m).range ≤
    omegaRangeSub m B

/-- The constructive block peeling puts the desired range subgroup inside
the exact outer stable hull. -/
theorem omegaRangeSub_le_outerStableHull {m : ℕ} (hm : 0 < m)
    {B : Set E} (h0 : (0 : E) ∈ B) :
    omegaRangeSub m B ≤
      HNNDescent.stableHull (slimShiftRangeEquiv m) (slimWBase m B) := by
  rintro y ⟨x, hx, rfl⟩
  apply slimPiF3Hom_mem_outerStableHull_iff.mpr
  exact ASub_omegaOp_le hm (slimTower m) h0 hx

/-- If the static seam holds, adjoining the desired range subgroup to the
stage-two alphabet is already edge-stable. -/
theorem stable_sup_omegaRangeSub_of_staticSeam {m : ℕ} {B : Set E}
    (hseam : StaticSeam m B) :
    HNNDescent.Stable (slimShiftRangeEquiv m)
      (slimWBase m B ⊔ omegaRangeSub m B) := by
  have hstable := stable_map_slimPiF3Hom_ASub_omega m B
  constructor
  · intro a ha
    have haX : (a : SlimPi m) ∈ omegaRangeSub m B :=
      hseam ⟨ha, a.property⟩
    exact Subgroup.mem_sup_right (hstable.fwd a haX)
  · intro b hb
    have hbX : (b : SlimPi m) ∈ omegaRangeSub m B :=
      hseam ⟨hb, b.property⟩
    exact Subgroup.mem_sup_right (hstable.bwd b hbX)

/-- **Static-seam reduction of the exact stable-hull computation.** -/
theorem slimPiF3Hom_mem_ASub_omega_of_outerStableHull_of_staticSeam
    {m : ℕ} {B : Set E} (hseam : StaticSeam m B) (x : F₃)
    (hx : slimPiF3Hom m x ∈
      HNNDescent.stableHull (slimShiftRangeEquiv m) (slimWBase m B)) :
    x ∈ ASub (omegaOp m B) := by
  have hle : HNNDescent.stableHull
      (slimShiftRangeEquiv m) (slimWBase m B) ≤
        slimWBase m B ⊔ omegaRangeSub m B :=
    HNNDescent.stableHull_le (slimShiftRangeEquiv m)
      le_sup_left (stable_sup_omegaRangeSub_of_staticSeam hseam)
  have hxX : slimPiF3Hom m x ∈ omegaRangeSub m B :=
    hseam ⟨hle hx, ⟨x, rfl⟩⟩
  obtain ⟨y, hy, hyx⟩ := hxX
  have : y = x := slimPiF3Hom_injective m hyx
  rwa [this] at hy

/-- With positivity and the zero block, the stable hull is exactly the join
of the original alphabet and the desired embedded Omega subgroup. -/
theorem outerStableHull_eq_sup_of_staticSeam {m : ℕ} (hm : 0 < m)
    {B : Set E} (h0 : (0 : E) ∈ B) (hseam : StaticSeam m B) :
    HNNDescent.stableHull (slimShiftRangeEquiv m) (slimWBase m B) =
      slimWBase m B ⊔ omegaRangeSub m B := by
  apply le_antisymm
  · exact HNNDescent.stableHull_le (slimShiftRangeEquiv m)
      le_sup_left (stable_sup_omegaRangeSub_of_staticSeam hseam)
  · exact sup_le
      (HNNDescent.le_stableHull (slimShiftRangeEquiv m) (slimWBase m B))
      (omegaRangeSub_le_outerStableHull hm h0)

end Omega
end Higman
end GroupApproximation
