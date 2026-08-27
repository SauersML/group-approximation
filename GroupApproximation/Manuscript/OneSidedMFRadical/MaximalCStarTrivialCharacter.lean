import GroupApproximation.Analysis.MaximalCStarKazhdanProjection

/-!
# The trivial character and orthogonal-corner unitization

This file supplies the two algebraic ingredients used to turn a nonunital
corner inclusion into a unital representation of a maximal group C-star
algebra: the integrated trivial character, and the sum of two nonunital star
homomorphisms with mutually orthogonal ranges.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open MaximalCStarKazhdanProjection

noncomputable section

universe u v

/-! ## The integrated trivial character -/

/-- The canonical character of `Cmax(K)` obtained by integrating the trivial
one-dimensional unitary representation. -/
noncomputable def maximalGroupCStarTrivialCharacter
    (K : Type u) [Group K] : MaximalGroupCStar K →⋆ₐ[ℂ] ℂ :=
  (maximalGroupCStar_existsUnique_lift_allUniverses K
    (trivialRep K ℂ)).choose

/-- The integrated trivial character sends every canonical group unitary to
one. -/
@[simp] theorem maximalGroupCStarTrivialCharacter_generator
    (K : Type u) [Group K] (k : K) :
    maximalGroupCStarTrivialCharacter K
        (maximalGroupCStarGenerator K k) = 1 :=
  (maximalGroupCStar_existsUnique_lift_allUniverses K
    (trivialRep K ℂ)).choose_spec.1 k

/-- The integrated trivial character sends the orbit average to one. -/
@[simp] theorem maximalGroupCStarTrivialCharacter_average
    {K : Type u} [Group K] (KD : KazhdanData K) :
    maximalGroupCStarTrivialCharacter K KD.average = 1 :=
  image_average_eq_one KD (maximalGroupCStarTrivialCharacter K)
    (maximalGroupCStarTrivialCharacter_generator K)

/-- The integrated trivial character sends the maximal Kazhdan projection to
one. -/
@[simp] theorem maximalGroupCStarTrivialCharacter_kazhdanProjection
    {K : Type u} [Group K] (KD : KazhdanData K) :
    maximalGroupCStarTrivialCharacter K KD.projection = 1 :=
  image_projection_eq_one KD (maximalGroupCStarTrivialCharacter K)
    (maximalGroupCStarTrivialCharacter_generator K)

/-- The trivial character is the unique star homomorphism to `ℂ` which sends
every canonical group unitary to one. -/
theorem maximalGroupCStarTrivialCharacter_unique
    (K : Type u) [Group K] (f : MaximalGroupCStar K →⋆ₐ[ℂ] ℂ)
    (hf : ∀ k : K, f (maximalGroupCStarGenerator K k) = 1) :
    f = maximalGroupCStarTrivialCharacter K :=
  maximalGroupCStar_lift_unique K f (maximalGroupCStarTrivialCharacter K)
    (fun k ↦ (hf k).trans
      (maximalGroupCStarTrivialCharacter_generator K k).symm)

/-! ## Sums of orthogonal nonunital star homomorphisms -/

/-- Two nonunital star homomorphisms with mutually annihilating ranges and
whose units add to the target unit sum to a unital star homomorphism. -/
noncomputable def orthogonalSumStarAlgHom
    {C : Type u} {A : Type v} [CStarAlgebra C] [CStarAlgebra A]
    (f g : C →⋆ₙₐ[ℂ] A)
    (hfg : ∀ a b : C, f a * g b = 0)
    (hgf : ∀ a b : C, g a * f b = 0)
    (hone : f 1 + g 1 = 1) : C →⋆ₐ[ℂ] A where
  toFun a := f a + g a
  map_one' := hone
  map_zero' := by simp
  map_add' a b := by
    rw [map_add, map_add]
    abel
  map_mul' a b := by
    rw [map_mul, map_mul, mul_add, add_mul, add_mul, hfg a b, hgf a b,
      zero_add, add_zero]
  commutes' c := by
    calc
      f (algebraMap ℂ C c) + g (algebraMap ℂ C c) =
          f (c • (1 : C)) + g (c • (1 : C)) := by
            rw [Algebra.smul_def, mul_one]
      _ = c • (f 1 + g 1) := by
            rw [map_smul, map_smul, smul_add]
      _ = c • (1 : A) := by rw [hone]
      _ = algebraMap ℂ A c := by rw [Algebra.smul_def, mul_one]
  map_star' a := by
    rw [map_star, map_star, star_add]

@[simp] theorem orthogonalSumStarAlgHom_apply
    {C : Type u} {A : Type v} [CStarAlgebra C] [CStarAlgebra A]
    (f g : C →⋆ₙₐ[ℂ] A)
    (hfg : ∀ a b : C, f a * g b = 0)
    (hgf : ∀ a b : C, g a * f b = 0)
    (hone : f 1 + g 1 = 1) (a : C) :
    orthogonalSumStarAlgHom f g hfg hgf hone a = f a + g a :=
  rfl

/-- A character placed on a star projection gives a nonunital star
homomorphism into that projection corner. -/
noncomputable def characterProjectionNonUnitalStarAlgHom
    {C : Type u} {A : Type v} [CStarAlgebra C] [CStarAlgebra A]
    (chi : C →⋆ₐ[ℂ] ℂ) (r : A)
    (hrstar : star r = r) (hrid : r * r = r) : C →⋆ₙₐ[ℂ] A where
  toFun a := (chi a) • r
  map_smul' c a := by
    rw [map_smul, smul_smul]
    change (c * chi a) • r = (c * chi a) • r
    rfl
  map_zero' := by simp
  map_add' a b := by
    rw [map_add, add_smul]
  map_mul' a b := by
    rw [map_mul, smul_mul_smul_comm, hrid]
  map_star' a := by
    rw [map_star, star_smul, hrstar]

@[simp] theorem characterProjectionNonUnitalStarAlgHom_apply
    {C : Type u} {A : Type v} [CStarAlgebra C] [CStarAlgebra A]
    (chi : C →⋆ₐ[ℂ] ℂ) (r : A)
    (hrstar : star r = r) (hrid : r * r = r) (a : C) :
    characterProjectionNonUnitalStarAlgHom chi r hrstar hrid a =
      (chi a) • r :=
  rfl

/-- Unitize a nonunital star homomorphism by placing a character on the
complement of its support projection. -/
noncomputable def complementUnitizedStarAlgHom
    {C : Type u} {A : Type v} [CStarAlgebra C] [CStarAlgebra A]
    (e : C →⋆ₙₐ[ℂ] A) (chi : C →⋆ₐ[ℂ] ℂ) : C →⋆ₐ[ℂ] A := by
  let p : A := e 1
  let r : A := 1 - p
  have hpstar : star p = p := by
    change star (e (1 : C)) = e 1
    rw [← map_star]
    simp
  have hpid : p * p = p := by
    change e (1 : C) * e 1 = e 1
    rw [← map_mul]
    simp
  have hrstar : star r = r := by
    change star (1 - p) = 1 - p
    rw [star_sub, star_one, hpstar]
  have hrid : r * r = r := by
    change (1 - p) * (1 - p) = 1 - p
    rw [sub_mul, one_mul, mul_sub, mul_one, hpid, sub_self, sub_zero]
  let g : C →⋆ₙₐ[ℂ] A :=
    characterProjectionNonUnitalStarAlgHom chi r hrstar hrid
  have hfg : ∀ a b : C, e a * g b = 0 := by
    intro a b
    have hap : e a * p = e a := by
      change e a * e (1 : C) = e a
      rw [← map_mul]
      simp
    have har : e a * r = 0 := by
      change e a * (1 - p) = 0
      rw [mul_sub, mul_one, hap, sub_self]
    change e a * ((chi b) • r) = 0
    rw [mul_smul_comm, har, smul_zero]
  have hgf : ∀ a b : C, g a * e b = 0 := by
    intro a b
    have hpb : p * e b = e b := by
      change e (1 : C) * e b = e b
      rw [← map_mul]
      simp
    have hrb : r * e b = 0 := by
      change (1 - p) * e b = 0
      rw [sub_mul, one_mul, hpb, sub_self]
    change ((chi a) • r) * e b = 0
    rw [smul_mul_assoc, hrb, smul_zero]
  have hone : e 1 + g 1 = 1 := by
    change p + (chi 1) • r = 1
    rw [map_one, one_smul]
    change p + (1 - p) = 1
    abel
  exact orthogonalSumStarAlgHom e g hfg hgf hone

@[simp] theorem complementUnitizedStarAlgHom_apply
    {C : Type u} {A : Type v} [CStarAlgebra C] [CStarAlgebra A]
    (e : C →⋆ₙₐ[ℂ] A) (chi : C →⋆ₐ[ℂ] ℂ) (a : C) :
    complementUnitizedStarAlgHom e chi a =
      e a + (chi a) • ((1 : A) - e 1) := by
  rfl

end


end OneSidedMFRadical
end Manuscript
end GroupApproximation
