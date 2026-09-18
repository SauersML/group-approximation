import GroupApproximation.Analysis.CStarIdealApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Arveson pairs, step 1: the quotient-norm limit

Lane TWWSchafhauser-3a1, work order WO-TWWSchafhauser-3a-1.  This is the first
of the files proving `exists_arvesonPair` (Arveson, *Notes on extensions of
C⋆-algebras*, Duke Math. J. 44 (1977), §1; Davidson, *C⋆-algebras by example*,
I.9.16).

For a unital ⋆-homomorphism `π : B →⋆ₐ[ℂ] C` of C⋆-algebras, surjective or not,
let `J = ker π`.  The factored map `B ⧸ J → C` is an injective ⋆-homomorphism
of C⋆-algebras, hence isometric, so `‖π x‖` is the quotient norm of `x`.  For
the approximate unit `e` of `J` built in `CStarIdealApproximateUnit`, this
gives eventually `‖x - e x‖ ≤ ‖π x‖ + δ`: split `x` into a near-optimal
representative `x - j` and `j ∈ J`, contract the first part by `1 - e`, and
absorb the second part by the unit.

* `arvesonKernel π` is `ker π`, with the instances the quotient needs.
* `arvesonKernel_norm_mk`: `‖x + J‖ = ‖π x‖`.
* `arvesonKernel_exists_near`: some `j ∈ J` has `‖x - j‖ < ‖π x‖ + δ`.
* `arvesonPair_eventually_absorb_finset`: eventually along the approximate
  unit, `‖x - e x‖ ≤ ‖π x‖ + δ` for all `x` in a finite set.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

open Filter

noncomputable section

universe v w

variable {B : Type v} {C : Type w} [CStarAlgebra B] [CStarAlgebra C]

/-- The kernel of `π`, as a closed star-stable two-sided ideal. -/
def arvesonKernel (π : B →⋆ₐ[ℂ] C) : Ideal B :=
  RingHom.ker π

theorem mem_arvesonKernel_iff (π : B →⋆ₐ[ℂ] C) (a : B) :
    a ∈ arvesonKernel π ↔ π a = 0 :=
  RingHom.mem_ker

instance arvesonKernel_isTwoSided (π : B →⋆ₐ[ℂ] C) :
    (arvesonKernel π).IsTwoSided where
  mul_mem_of_left := by
    intro a b ha
    rw [mem_arvesonKernel_iff] at ha ⊢
    rw [map_mul, ha, zero_mul]

instance arvesonKernel_isStarStable (π : B →⋆ₐ[ℂ] C) :
    CStarTensor.IsStarStable (arvesonKernel π) where
  star_mem := by
    intro a ha
    rw [mem_arvesonKernel_iff] at ha ⊢
    rw [map_star, ha, star_zero]

instance arvesonKernel_isClosed (π : B →⋆ₐ[ℂ] C) :
    IsClosed ((arvesonKernel π : Ideal B) : Set B) := by
  have hset : ((arvesonKernel π : Ideal B) : Set B) = π ⁻¹' {0} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    exact mem_arvesonKernel_iff π a
  rw [hset]
  exact IsClosed.preimage (map_continuous π) isClosed_singleton

/-- `π` factored through its kernel. -/
def arvesonLift [Nontrivial B] (π : B →⋆ₐ[ℂ] C) :
    (B ⧸ arvesonKernel π) →⋆ₐ[ℂ] C :=
  CStarTensor.quotientStarLift (arvesonKernel π) π
    (fun a ha ↦ (mem_arvesonKernel_iff π a).mp ha)

theorem arvesonLift_mk [Nontrivial B] (π : B →⋆ₐ[ℂ] C) (a : B) :
    arvesonLift π (Ideal.Quotient.mk (arvesonKernel π) a) = π a :=
  CStarTensor.quotientStarLift_mk _ _ _ a

theorem arvesonLift_injective [Nontrivial B] (π : B →⋆ₐ[ℂ] C) :
    Function.Injective (arvesonLift π) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [arvesonLift_mk, arvesonLift_mk] at hxy
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, mem_arvesonKernel_iff, map_sub, hxy,
    sub_self]

/-- **The quotient norm is the norm of the image**: the factored map is an
injective ⋆-homomorphism of C⋆-algebras, hence isometric. -/
theorem arvesonKernel_norm_mk [Nontrivial B] (π : B →⋆ₐ[ℂ] C) (x : B) :
    ‖Ideal.Quotient.mk (arvesonKernel π) x‖ = ‖π x‖ := by
  have h := NonUnitalStarAlgHom.norm_map (arvesonLift π) (arvesonLift_injective π)
    (Ideal.Quotient.mk (arvesonKernel π) x)
  rw [arvesonLift_mk] at h
  exact h.symm

/-- Some element of the kernel brings `x` within `‖π x‖ + δ`. -/
theorem arvesonKernel_exists_near [Nontrivial B] (π : B →⋆ₐ[ℂ] C) (x : B)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ j ∈ arvesonKernel π, ‖x - j‖ < ‖π x‖ + δ := by
  obtain ⟨r, hr, hrn⟩ := CStarTensor.quotient_norm_mk_lt (arvesonKernel π)
    (Ideal.Quotient.mk (arvesonKernel π) x) hδ
  refine ⟨x - r, ?_, ?_⟩
  · rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact hr.symm
  · rw [sub_sub_cancel]
    calc ‖r‖ < ‖Ideal.Quotient.mk (arvesonKernel π) x‖ + δ := hrn
      _ = ‖π x‖ + δ := by rw [arvesonKernel_norm_mk]

/-- The approximate unit of the kernel used throughout the construction. -/
def arvesonUnit [Nontrivial B] (π : B →⋆ₐ[ℂ] C) :
    CStarTensor.IdealApproximateUnit (arvesonKernel π) :=
  CStarTensor.idealApproximateUnit (arvesonKernel π)

/-- **The quotient-norm limit, upper half**: eventually along the approximate
unit of the kernel, `‖x - e x‖ ≤ ‖π x‖ + δ`. -/
theorem arvesonPair_eventually_absorb [Nontrivial B] (π : B →⋆ₐ[ℂ] C) (x : B)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ e in (arvesonUnit π).filter, ‖x - e * x‖ ≤ ‖π x‖ + δ := by
  obtain ⟨j, hj, hjn⟩ := arvesonKernel_exists_near π x (half_pos hδ)
  have hsj : star j ∈ arvesonKernel π := CStarTensor.IsStarStable.star_mem hj
  filter_upwards [(arvesonUnit π).eventually_isSelfAdjoint,
    (arvesonUnit π).eventually_norm_one_sub,
    ((arvesonUnit π).tendsto_mul_right (star j) hsj).eventually_lt_const
      (half_pos hδ)] with e hesa hone hsmall
  have hstar : ‖j - e * j‖ = ‖star j - star j * e‖ := by
    rw [← norm_star (j - e * j), star_sub, star_mul, hesa.star_eq]
  have hsplit : x - e * x = (1 - e) * (x - j) + (j - e * j) := by
    simp only [sub_mul, mul_sub, one_mul]
    abel
  have hfirst : ‖(1 - e) * (x - j)‖ ≤ ‖x - j‖ :=
    (norm_mul_le _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hone)
  have hsecond : ‖j - e * j‖ ≤ δ / 2 := by
    rw [hstar]
    exact hsmall.le
  calc ‖x - e * x‖ = ‖(1 - e) * (x - j) + (j - e * j)‖ := by rw [hsplit]
    _ ≤ ‖(1 - e) * (x - j)‖ + ‖j - e * j‖ := norm_add_le _ _
    _ ≤ ‖x - j‖ + δ / 2 := add_le_add hfirst hsecond
    _ ≤ ‖π x‖ + δ := by linarith

/-- The absorption bound, jointly over a finite set. -/
theorem arvesonPair_eventually_absorb_finset [Nontrivial B] (π : B →⋆ₐ[ℂ] C)
    (X : Finset B) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ e in (arvesonUnit π).filter, ∀ x ∈ X, ‖x - e * x‖ ≤ ‖π x‖ + δ :=
  (Filter.eventually_all_finset X).2 fun x _ ↦ arvesonPair_eventually_absorb π x hδ

end

end TWWSchafhauser
end Full
end GroupApproximation
