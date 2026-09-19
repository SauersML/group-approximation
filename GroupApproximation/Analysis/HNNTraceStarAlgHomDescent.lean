import GroupApproximation.Analysis.CStarIdealApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Closed ranges and descent for the HNN trace argument

This file contains the two general C-star-homomorphism facts used by the
trace-specific proof of HNN permanence: the range of a unital star-algebra
homomorphism is closed, and a homomorphism descends through a surjective one
when it kills its kernel.
-/

namespace GroupApproximation
namespace HNNTrace

open scoped CStarAlgebra

noncomputable section

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-- The kernel of a star-algebra homomorphism, as a two-sided star ideal. -/
private noncomputable def homKernel [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) : Ideal A :=
  RingHom.ker f

private theorem mem_homKernel_iff [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) (a : A) :
    a ∈ homKernel f ↔ f a = 0 :=
  RingHom.mem_ker

private instance homKernel_isTwoSided [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) : (homKernel f).IsTwoSided where
  mul_mem_of_left := by
    intro a b ha
    rw [mem_homKernel_iff] at ha ⊢
    rw [map_mul, ha, zero_mul]

private instance homKernel_isStarStable [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) : CStarTensor.IsStarStable (homKernel f) where
  star_mem := by
    intro a ha
    rw [mem_homKernel_iff] at ha ⊢
    rw [map_star, ha, star_zero]

private instance homKernel_isClosed [CStarAlgebra A] [CStarAlgebra B]
    (f : A →⋆ₐ[ℂ] B) : IsClosed ((homKernel f : Ideal A) : Set A) := by
  have hset : ((homKernel f : Ideal A) : Set A) = f ⁻¹' {0} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    exact mem_homKernel_iff f a
  rw [hset]
  exact IsClosed.preimage (map_continuous f) isClosed_singleton

/-- A C-star homomorphism factored through its kernel. -/
private noncomputable def quotientRangeHom [CStarAlgebra A] [CStarAlgebra B]
    [Nontrivial A] [Nontrivial B] (f : A →⋆ₐ[ℂ] B) :
    (A ⧸ homKernel f) →⋆ₐ[ℂ] B :=
  CStarTensor.quotientStarLift (homKernel f) f
    (fun a ha ↦ (mem_homKernel_iff f a).mp ha)

@[simp] private theorem quotientRangeHom_mk [CStarAlgebra A] [CStarAlgebra B]
    [Nontrivial A] [Nontrivial B] (f : A →⋆ₐ[ℂ] B) (a : A) :
    quotientRangeHom f (Ideal.Quotient.mk (homKernel f) a) = f a :=
  CStarTensor.quotientStarLift_mk _ _ _ a

private theorem quotientRangeHom_injective [CStarAlgebra A] [CStarAlgebra B]
    [Nontrivial A] [Nontrivial B] (f : A →⋆ₐ[ℂ] B) :
    Function.Injective (quotientRangeHom f) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [quotientRangeHom_mk, quotientRangeHom_mk] at hxy
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, mem_homKernel_iff, map_sub, hxy,
    sub_self]

/-- The range of a unital star-algebra homomorphism between C-star algebras
is closed. -/
theorem isClosed_range_starAlgHom [CStarAlgebra A] [CStarAlgebra B]
    [Nontrivial A] [Nontrivial B] (f : A →⋆ₐ[ℂ] B) :
    IsClosed (Set.range f) := by
  have hrange : Set.range f = Set.range (quotientRangeHom f) := by
    ext b
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨Ideal.Quotient.mk (homKernel f) a, quotientRangeHom_mk f a⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨a, (quotientRangeHom_mk f a).symm⟩
  rw [hrange]
  have hiso : Isometry (quotientRangeHom f) :=
    NonUnitalStarAlgHom.isometry _ (quotientRangeHom_injective f)
  exact hiso.isUniformInducing.isComplete_range.isClosed

/-- Two source elements have the same image under the descended homomorphism
as soon as they have the same image under the quotient map. -/
private theorem target_eq_of_source_eq [CStarAlgebra A] [CStarAlgebra B]
    [CStarAlgebra C] (q : A →⋆ₐ[ℂ] B) (r : A →⋆ₐ[ℂ] C)
    (hker : ∀ a : A, q a = 0 → r a = 0) {a b : A} (hab : q a = q b) :
    r a = r b := by
  have hq : q (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hr := hker (a - b) hq
  rw [map_sub, sub_eq_zero] at hr
  exact hr

/-- Descend `r` through a surjective `q`, under the literal kernel condition.
The definition uses a chosen preimage; `target_eq_of_source_eq` proves every
algebraic law and the computation theorem below removes the choice. -/
def descendStarAlgHom [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
    (q : A →⋆ₐ[ℂ] B) (r : A →⋆ₐ[ℂ] C)
    (hq : Function.Surjective q)
    (hker : ∀ a : A, q a = 0 → r a = 0) : B →⋆ₐ[ℂ] C where
  toFun b := r (Classical.choose (hq b))
  map_one' := (target_eq_of_source_eq q r hker
    ((Classical.choose_spec (hq 1)).trans (map_one q).symm)).trans (map_one r)
  map_zero' := (target_eq_of_source_eq q r hker
    ((Classical.choose_spec (hq 0)).trans (map_zero q).symm)).trans (map_zero r)
  map_add' b₁ b₂ := target_eq_of_source_eq q r hker (by
    calc
      q (Classical.choose (hq (b₁ + b₂))) = b₁ + b₂ :=
        Classical.choose_spec (hq (b₁ + b₂))
      _ = q (Classical.choose (hq b₁)) + q (Classical.choose (hq b₂)) := by
        rw [Classical.choose_spec (hq b₁), Classical.choose_spec (hq b₂)]
      _ = q (Classical.choose (hq b₁) + Classical.choose (hq b₂)) :=
        (map_add q _ _).symm) |>.trans (map_add r _ _)
  map_mul' b₁ b₂ := target_eq_of_source_eq q r hker (by
    calc
      q (Classical.choose (hq (b₁ * b₂))) = b₁ * b₂ :=
        Classical.choose_spec (hq (b₁ * b₂))
      _ = q (Classical.choose (hq b₁)) * q (Classical.choose (hq b₂)) := by
        rw [Classical.choose_spec (hq b₁), Classical.choose_spec (hq b₂)]
      _ = q (Classical.choose (hq b₁) * Classical.choose (hq b₂)) :=
        (map_mul q _ _).symm) |>.trans (map_mul r _ _)
  commutes' z := target_eq_of_source_eq q r hker (by
    calc
      q (Classical.choose (hq (algebraMap ℂ B z))) = algebraMap ℂ B z :=
        Classical.choose_spec (hq (algebraMap ℂ B z))
      _ = q (algebraMap ℂ A z) := (q.commutes z).symm) |>.trans (r.commutes z)
  map_star' b := target_eq_of_source_eq q r hker (by
    calc
      q (Classical.choose (hq (star b))) = star b :=
        Classical.choose_spec (hq (star b))
      _ = star (q (Classical.choose (hq b))) := by
        rw [Classical.choose_spec (hq b)]
      _ = q (star (Classical.choose (hq b))) :=
        (map_star q _).symm) |>.trans (map_star r _)

@[simp] theorem descendStarAlgHom_apply [CStarAlgebra A] [CStarAlgebra B]
    [CStarAlgebra C] (q : A →⋆ₐ[ℂ] B) (r : A →⋆ₐ[ℂ] C)
    (hq : Function.Surjective q)
    (hker : ∀ a : A, q a = 0 → r a = 0) (b : B) :
    descendStarAlgHom q r hq hker b = r (Classical.choose (hq b)) :=
  by
    unfold descendStarAlgHom
    rfl

@[simp] theorem descendStarAlgHom_comp_apply [CStarAlgebra A] [CStarAlgebra B]
    [CStarAlgebra C] (q : A →⋆ₐ[ℂ] B) (r : A →⋆ₐ[ℂ] C)
    (hq : Function.Surjective q)
    (hker : ∀ a : A, q a = 0 → r a = 0) (a : A) :
    descendStarAlgHom q r hq hker (q a) = r a :=
  by
    rw [descendStarAlgHom_apply]
    exact target_eq_of_source_eq q r hker (Classical.choose_spec (hq (q a)))

end

end HNNTrace
end GroupApproximation
