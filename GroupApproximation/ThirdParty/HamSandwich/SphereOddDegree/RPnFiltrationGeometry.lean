import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnInclusionCohomology
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Hausdorff
import Mathlib

/-!
# Point-set geometry of the real-projective filtration

This module contains the lower-subspace geometry used by the affine-cover
computation.  Its declarations are deliberately separate from the stronger
explicit cofiber-homeomorphism construction.
-/

noncomputable section

open CategoryTheory

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

def affineRpLowerSubspace (n : ℕ) : Set (RP (n + 1)) := Set.range (rpInclusion n)

theorem affineRpLowerSubspace_eq_image (n : ℕ) :
    affineRpLowerSubspace n = proj (n + 1) '' Set.range (sphereInclusion n) := by
  ext q
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := RP.exists_rep a
    exact ⟨sphereInclusion n x, ⟨x, rfl⟩, rpInclusion_proj n x⟩
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨proj n x, rpInclusion_proj n x⟩

theorem isCompact_affineRpLowerSubspace (n : ℕ) : IsCompact (affineRpLowerSubspace n) := by
  rw [affineRpLowerSubspace, ← Set.image_univ]
  exact isCompact_univ.image (rpInclusion n).continuous

theorem isClosed_affineRpLowerSubspace (n : ℕ) : IsClosed (affineRpLowerSubspace n) :=
  (isCompact_affineRpLowerSubspace n).isClosed

def affineElast (n : ℕ) : EuclideanSpace ℝ (Fin (n + 2)) :=
  EuclideanSpace.single (Fin.last (n + 1)) 1

theorem affineElast_norm (n : ℕ) : ‖affineElast n‖ = 1 := by simp [affineElast]

/-- Pairing against the last basis vector reads off the last coordinate. -/
theorem inner_affineElast (n : ℕ) (v : EuclideanSpace ℝ (Fin (n + 2))) :
    inner ℝ (affineElast n) v = v (Fin.last (n + 1)) := by
  rw [affineElast, EuclideanSpace.inner_single_left]
  simp

theorem proj_mem_affineLowerSubspace_of_last_zero (n : ℕ) (x : Sphere (n + 1))
    (hx : (x : EuclideanSpace ℝ (Fin (n + 2))) (Fin.last (n + 1)) = 0) :
    proj (n + 1) x ∈ affineRpLowerSubspace n := by
  refine ⟨proj n ⟨WithLp.equiv 2 _ |>.symm <| Fin.init <| WithLp.equiv 2 _ x.1, ?_⟩, ?_⟩
  · cases x
    simp_all +decide [EuclideanSpace.norm_eq, Fin.sum_univ_castSucc]
    rename_i h
    replace h := mem_sphere_zero_iff_norm.mp h
    simp_all +decide [EuclideanSpace.norm_eq, Fin.sum_univ_castSucc]
    simpa [Fin.init] using h
  · convert rpInclusion_proj n _
    ext i
    induction i using Fin.lastCases <;> aesop

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
