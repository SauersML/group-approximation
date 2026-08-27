import GroupApproximation.Higman.OmegaTowerSelectedArbitraryTargetClassifier
import GroupApproximation.Higman.OmegaTowerStaticSeamOrbit

/-!
# Closing the static Omega seam

The arbitrary-target selected normal form shows that every orbit label which
returns to the row alphabet is again a canonical Omega label.  Passing this
literal alphabet inclusion through free-group closure closes the last static
intersection in the slim tower.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- A selected-code orbit label which lies in the full row-label range is a
canonical label indexed by `omegaOp m B`. -/
theorem slimOmegaOrbitLabelSet_inter_rows_le_omegaLabelSet
    {m : ℕ} (hm : 0 < m) {B : Set E} (hzero : (0 : E) ∈ B) :
    slimOmegaOrbitLabelSet m B ∩ Set.range (slimRowLabel m) ⊆
      omegaLabelSet m B := by
  rintro _ ⟨horbit, ⟨q, rfl⟩⟩
  obtain ⟨g, hg, r, hrOmega, hreturn⟩ := horbit
  obtain ⟨_, ⟨l, hlOmega, rfl⟩, rfl⟩ := hrOmega
  obtain ⟨f, hfOmega, hq⟩ :=
    exists_omega_target_of_selected_rightLabel_return
      hm hzero hlOmega hg hreturn.symm
  refine ⟨bK f, ⟨f, hfOmega, rfl⟩, ?_⟩
  rw [hq]

/-- The orbit/row boundary subgroup is contained in the exact free
coordinate subgroup of the desired Omega range. -/
theorem closure_orbit_rows_le_omegaLabelSub
    {m : ℕ} (hm : 0 < m) {B : Set E} (hzero : (0 : E) ∈ B) :
    Subgroup.closure (FreeGroup.of ''
        (slimOmegaOrbitLabelSet m B ∩ Set.range (slimRowLabel m))) ≤
      omegaLabelSub m B := by
  unfold omegaLabelSub
  exact Subgroup.closure_mono (Set.image_mono
    (slimOmegaOrbitLabelSet_inter_rows_le_omegaLabelSet hm hzero))

/-- The stage-two static seam is unconditional for positive block length and
an input alphabet containing the zero sequence. -/
theorem staticSeam_slim
    {m : ℕ} (hm : 0 < m) {B : Set E} (hzero : (0 : E) ∈ B) :
    StaticSeam m B := by
  intro z hz
  obtain ⟨v, hzv, hvBoundary⟩ :=
    exists_orbit_boundary_cbWord_of_mem_slimJoin_range
      hzero hz.1 hz.2
  have hvOmega : slimLabelHom m v ∈ omegaLabelSub m B :=
    closure_orbit_rows_le_omegaLabelSub hm hzero hvBoundary
  rw [omegaRangeSub_eq_map_omegaLabelSub]
  refine ⟨slimLabelHom m v, hvOmega, ?_⟩
  have hfree := DFunLike.congr_fun
    (slimPiF3Hom_comp_cbHom_eq_freeLabel m) v
  exact (hzv.trans hfree).symm

/-- The hard intersection half of `TowerClosure` for the concrete slim
tower. -/
theorem slimTower_descent
    {m : ℕ} (hm : 0 < m) {B : Set E} (hzero : (0 : E) ∈ B) :
    ∀ x : F₃, slimOmegaEmb m x ∈ W (slimTower m) B →
      x ∈ ASub (omegaOp m B) := by
  apply slimTower_descent_of_outerStableHull
  intro x hx
  exact slimPiF3Hom_mem_ASub_omega_of_outerStableHull_of_staticSeam
    (staticSeam_slim hm hzero) x hx

end Omega
end Higman
end GroupApproximation
