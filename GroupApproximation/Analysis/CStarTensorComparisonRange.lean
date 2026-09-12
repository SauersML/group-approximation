import GroupApproximation.Analysis.CStarTensorComparison
import GroupApproximation.Analysis.CStarIdealApproximateUnit

/-!
# The comparison map is surjective

`CStarTensorComparison` builds `maxToMin : A ⊗_max B → A ⊗_min B` and proves
its range **dense**, stopping there because density is what elementary
arguments give.  This module closes the gap and proves the range is everything.

## The argument

It is the classical one, and every step of it exists in this development only
because two separate lanes landed their pieces:

1. `ker maxToMin` is a closed star-stable two-sided ideal — closed because the
   map is continuous, star-stable and two-sided because it is a
   ⋆-homomorphism.
2. The quotient by it is a C⋆-algebra.  This is *not* formal: the C⋆-identity
   for a quotient norm needs an approximate unit of the ideal, which
   `CStarIdealApproximateUnit` constructs.
3. The induced map on the quotient is injective, hence **isometric** — the
   theorem that an injective ⋆-homomorphism of complex C⋆-algebras preserves
   norms.
4. An isometry defined on a complete space has complete, therefore closed,
   range; and `range maxToMin` is exactly the range of the induced map,
   because the quotient map is surjective.
5. A dense closed set is everything.

So the surjection rests on the quotient theorem and on Mathlib's isometry
theorem, neither of which is a triviality, which is why
`CStarTensorComparison` declined to claim it and named its result for the
density it had actually proved.

## What this makes available

With `maxToMin_surjective` the comparison map is a surjection whose kernel
measures the failure of the two norms to agree
(`maxToMin_injective_iff`), so `A ⊗_min B` is exhibited as a quotient of
`A ⊗_max B` — the standard picture, and the one in which nuclearity says the
quotient map is an isomorphism.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `SO.16` and `RE.05`
remain **MISSING**.
-/

namespace GroupApproximation
namespace CStarTensor

open scoped TensorProduct CStarAlgebra

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
  [Nontrivial A] [Nontrivial B]

/-! ## The maximal tensor product is nontrivial -/

/-- `A ⊗_max B` is nontrivial: the image of `1 ⊗ₜ 1` has norm one, by the
cross-norm identity.  The quotient machinery below asks for this. -/
instance nontrivialMaxTensorProduct : Nontrivial (MaxTensorProduct A B) := by
  refine ⟨⟨maxTensorIn A B ((1 : A) ⊗ₜ[ℂ] (1 : B)), 0, ?_⟩⟩
  intro h
  have hn : ‖maxTensorIn A B ((1 : A) ⊗ₜ[ℂ] (1 : B))‖ = 1 := by
    rw [norm_maxTensorIn_tmul, CStarRing.norm_one, CStarRing.norm_one, mul_one]
  rw [h, norm_zero] at hn
  exact one_ne_zero hn.symm

/-! ## The kernel -/

/-- The kernel of the comparison map. -/
noncomputable def maxToMinKer : Ideal (MaxTensorProduct A B) :=
  RingHom.ker (maxToMin (A := A) (B := B))

theorem mem_maxToMinKer_iff (z : MaxTensorProduct A B) :
    z ∈ (maxToMinKer : Ideal (MaxTensorProduct A B)) ↔ maxToMin z = 0 :=
  RingHom.mem_ker

instance maxToMinKer_isTwoSided :
    (maxToMinKer (A := A) (B := B)).IsTwoSided where
  mul_mem_of_left := by
    intro a b ha
    rw [mem_maxToMinKer_iff] at ha ⊢
    rw [map_mul, ha, zero_mul]

instance maxToMinKer_isStarStable :
    IsStarStable (maxToMinKer (A := A) (B := B)) where
  star_mem := by
    intro a ha
    rw [mem_maxToMinKer_iff] at ha ⊢
    rw [StarHomClass.map_star, ha, star_zero]

instance maxToMinKer_isClosed :
    IsClosed ((maxToMinKer (A := A) (B := B)) :
      Set (MaxTensorProduct A B)) := by
  have hset : ((maxToMinKer (A := A) (B := B)) : Set (MaxTensorProduct A B))
      = (maxToMin (A := A) (B := B)) ⁻¹' {0} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    exact mem_maxToMinKer_iff z
  rw [hset]
  exact IsClosed.preimage (continuous_of_maxTensorProduct maxToMin)
    isClosed_singleton

/-! ## The induced map on the quotient -/

/-- The comparison map, factored through its kernel. -/
noncomputable def maxToMinQuotient :
    (MaxTensorProduct A B ⧸ maxToMinKer) →⋆ₐ[ℂ] MinTensorProduct A B :=
  quotientStarLift maxToMinKer maxToMin
    (fun _ ha ↦ (mem_maxToMinKer_iff _).mp ha)

@[simp] theorem maxToMinQuotient_mk (z : MaxTensorProduct A B) :
    maxToMinQuotient (Ideal.Quotient.mk maxToMinKer z) = maxToMin z :=
  quotientStarLift_mk _ _ _ z

/-- The induced map is injective: its kernel was divided out. -/
theorem maxToMinQuotient_injective :
    Function.Injective (maxToMinQuotient (A := A) (B := B)) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [maxToMinQuotient_mk, maxToMinQuotient_mk] at hxy
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, mem_maxToMinKer_iff, map_sub, hxy,
    sub_self]

/-- **The induced map is isometric.**  This is the theorem that an injective
⋆-homomorphism of complex C⋆-algebras preserves norms, applied on the quotient
— which is a C⋆-algebra only because of the approximate-unit construction. -/
theorem isometry_maxToMinQuotient :
    Isometry (maxToMinQuotient (A := A) (B := B)) :=
  NonUnitalStarAlgHom.isometry _ maxToMinQuotient_injective

/-! ## Closed range, and surjectivity -/

theorem range_maxToMin_eq_range_quotient :
    Set.range (maxToMin (A := A) (B := B))
      = Set.range (maxToMinQuotient (A := A) (B := B)) := by
  ext w
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Ideal.Quotient.mk maxToMinKer z, maxToMinQuotient_mk z⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨z, (maxToMinQuotient_mk z).symm⟩

/-- **The range is closed**: it is the range of an isometry defined on a
complete space, hence complete, hence closed. -/
theorem isClosed_range_maxToMin :
    IsClosed (Set.range (maxToMin (A := A) (B := B))) := by
  rw [range_maxToMin_eq_range_quotient]
  exact isometry_maxToMinQuotient.isUniformInducing.isComplete_range.isClosed

/-- **The comparison map is surjective.**  Its range is dense
(`denseRange_maxToMin`) and closed, so it is everything; `A ⊗_min B` is a
quotient of `A ⊗_max B`. -/
theorem maxToMin_surjective :
    Function.Surjective (maxToMin (A := A) (B := B)) := by
  rw [← Set.range_eq_univ]
  rw [← isClosed_range_maxToMin.closure_eq]
  exact denseRange_maxToMin.closure_eq

end CStarTensor
end GroupApproximation
