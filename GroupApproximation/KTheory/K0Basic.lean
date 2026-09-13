import GroupApproximation.KTheory.Functorial
import GroupApproximation.KTheory.K0Rect
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Operator `K₀`: equality, functoriality, orthogonal sums, the unit class

This file adds the working interface of `K₀` on top of the projection picture of
`Basic.lean` (`Cycle`, `VMonoid`, `KZero`) and the rectangular criterion of `K0Rect.lean`.

* `VMonoid.mk_eq_mk_iff`: equality of classes of projections is stable isomorphism.
* `KZero.mk_eq_mk_iff`: `[x] = [y]` in `K₀(A)` iff `x ⊞ z` and `y ⊞ z` are stably isomorphic
  for some cycle `z`.
* `KZero.hom_ext`: a homomorphism out of `K₀(A)` is determined by its values on classes of
  projections.
* `KZero.map_id`, `KZero.map_comp`: `K₀` is a functor along `*`-homomorphisms.
* `KZero.mk_add_of_mul_eq_zero`: `[p + q] = [p] + [q]` for orthogonal projections `p`, `q`.
* `KZero.unitClass`: the class `[1]` of a unital `A`, preserved by unital maps.
* `Cycle.rel_isometry_conj`: conjugating a projection by an isometry keeps its class.
-/

namespace GroupApproximation
namespace KTheory

open scoped Matrix

/-- Equality in the Grothendieck group of a commutative monoid. -/
theorem grothendieckAddGroup_of_eq_of_iff {M : Type*} [AddCommMonoid M] {a b : M} :
    Algebra.GrothendieckAddGroup.of a = Algebra.GrothendieckAddGroup.of b ↔
      ∃ c : M, c + a = c + b := by
  show AddLocalization.addMonoidOf (⊤ : AddSubmonoid M) a =
      AddLocalization.addMonoidOf (⊤ : AddSubmonoid M) b ↔ _
  rw [AddSubmonoid.LocalizationMap.eq_iff_exists]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc⟩, fun ⟨c, hc⟩ => ⟨⟨c, AddSubmonoid.mem_top c⟩, hc⟩⟩

namespace VMonoid

variable {A : Type*} [NonUnitalSemiring A] [StarRing A]

theorem mk_surjective : Function.Surjective (mk : Cycle A → VMonoid A) :=
  fun a => Quotient.exists_rep a

/-- **Equality of classes of projections is stable isomorphism.** -/
theorem mk_eq_mk_iff {x y : Cycle A} : mk x = mk y ↔ Cycle.Rel x y :=
  ⟨fun h => Quotient.exact h, mk_eq_mk_of_rel⟩

end VMonoid

namespace KZero

variable {A : Type*} [NonUnitalSemiring A] [StarRing A]

theorem mk_eq_mk_of_rel {x y : Cycle A} (h : Cycle.Rel x y) : mk x = mk y := by
  show Algebra.GrothendieckAddGroup.of (VMonoid.mk x) =
    Algebra.GrothendieckAddGroup.of (VMonoid.mk y)
  rw [VMonoid.mk_eq_mk_of_rel h]

/-- **Equality in `K₀`.** Two projections have the same class iff they become stably
isomorphic after adding a common projection. -/
theorem mk_eq_mk_iff {x y : Cycle A} :
    mk x = mk y ↔ ∃ z : Cycle A, Cycle.Rel (x + z) (y + z) := by
  show Algebra.GrothendieckAddGroup.of (VMonoid.mk x) =
      Algebra.GrothendieckAddGroup.of (VMonoid.mk y) ↔ _
  rw [grothendieckAddGroup_of_eq_of_iff]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨z, rfl⟩ := VMonoid.mk_surjective c
    rw [← VMonoid.mk_add, ← VMonoid.mk_add, VMonoid.mk_eq_mk_iff] at hc
    exact ⟨z, Cycle.rel_trans (Cycle.rel_add_comm x z)
      (Cycle.rel_trans hc (Cycle.rel_add_comm z y))⟩
  · rintro ⟨z, hz⟩
    refine ⟨VMonoid.mk z, ?_⟩
    rw [← VMonoid.mk_add, ← VMonoid.mk_add, VMonoid.mk_eq_mk_iff]
    exact Cycle.rel_trans (Cycle.rel_add_comm z x) (Cycle.rel_trans hz (Cycle.rel_add_comm y z))

/-- A homomorphism out of `K₀(A)` is determined by its values on classes of projections. -/
theorem hom_ext {G : Type*} [AddCommGroup G] {f g : KZero A →+ G}
    (h : ∀ x : Cycle A, f (mk x) = g (mk x)) : f = g := by
  apply Algebra.GrothendieckAddGroup.lift.symm.injective
  ext a
  obtain ⟨x, rfl⟩ := VMonoid.mk_surjective a
  exact h x

end KZero

namespace Cycle

variable {A B C : Type*} [NonUnitalSemiring A] [StarRing A] [NonUnitalSemiring B] [StarRing B]
  [NonUnitalSemiring C] [StarRing C]

@[simp] theorem map_id (x : Cycle A) : x.map (NonUnitalStarRingHom.id A) = x := by
  cases x; rfl

theorem map_comp (g : B →⋆ₙ+* C) (f : A →⋆ₙ+* B) (x : Cycle A) :
    x.map (g.comp f) = (x.map f).map g := by
  cases x; rfl

end Cycle

namespace KZero

variable {A B C : Type*} [NonUnitalSemiring A] [StarRing A] [NonUnitalSemiring B] [StarRing B]
  [NonUnitalSemiring C] [StarRing C]

/-- `K₀` sends the identity to the identity. -/
theorem map_id : map (NonUnitalStarRingHom.id A) = AddMonoidHom.id (KZero A) :=
  hom_ext fun x => by rw [map_mk, Cycle.map_id, AddMonoidHom.id_apply]

/-- `K₀` sends composites to composites. -/
theorem map_comp (g : B →⋆ₙ+* C) (f : A →⋆ₙ+* B) :
    map (g.comp f) = (map g).comp (map f) :=
  hom_ext fun x => by simp only [AddMonoidHom.comp_apply, map_mk, Cycle.map_comp]

end KZero

section RowsCols

variable {A : Type*} [NonUnitalSemiring A]

theorem fromRows_mul_fromCols_of_nonUnital {l₁ l₂ o o₁ o₂ : Type*} [Fintype o]
    (v₁ : Matrix l₁ o A) (v₂ : Matrix l₂ o A) (w₁ : Matrix o o₁ A) (w₂ : Matrix o o₂ A) :
    Matrix.fromRows v₁ v₂ * Matrix.fromCols w₁ w₂ =
      Matrix.fromBlocks (v₁ * w₁) (v₁ * w₂) (v₂ * w₁) (v₂ * w₂) := by
  ext (_ | _) (_ | _) <;> simp [Matrix.mul_apply]

theorem fromCols_mul_fromRows_of_nonUnital {l o o₁ o₂ : Type*} [Fintype o₁] [Fintype o₂]
    (v₁ : Matrix l o₁ A) (v₂ : Matrix l o₂ A) (w₁ : Matrix o₁ o A) (w₂ : Matrix o₂ o A) :
    Matrix.fromCols v₁ v₂ * Matrix.fromRows w₁ w₂ = v₁ * w₁ + v₂ * w₂ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type]

end RowsCols

namespace Cycle

variable {A : Type*} [NonUnitalSemiring A] [StarRing A]

/-- The block sum of two orthogonal projections is equivalent to their sum. -/
theorem rectMvN_add_of_mul_eq_zero {n : ℕ} {p q : Matrix (Fin n) (Fin n) A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) :
    RectMvN (⟨n, p, hp⟩ + ⟨n, q, hq⟩) ⟨n, p + q, hp.add hq hpq⟩ := by
  have hqp : q * p = 0 := by
    have h := congrArg Matrix.conjTranspose hpq
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_zero, ← Matrix.star_eq_conjTranspose,
      ← Matrix.star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] at h
  refine ⟨(Matrix.fromCols p q).submatrix id finSumFinEquiv.symm, ?_, ?_⟩
  · show ((Matrix.fromCols p q).submatrix id finSumFinEquiv.symm)ᴴ *
        (Matrix.fromCols p q).submatrix id finSumFinEquiv.symm =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p 0 0 q)
    rw [Matrix.conjTranspose_submatrix,
      ← Matrix.submatrix_mul (Matrix.fromCols p q)ᴴ (Matrix.fromCols p q)
        finSumFinEquiv.symm id finSumFinEquiv.symm Function.bijective_id,
      Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      fromRows_mul_fromCols_of_nonUnital, ← Matrix.star_eq_conjTranspose,
      ← Matrix.star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
      hp.isIdempotentElem.eq, hq.isIdempotentElem.eq, hpq, hqp, Matrix.reindex_apply]
  · show (Matrix.fromCols p q).submatrix id finSumFinEquiv.symm *
        ((Matrix.fromCols p q).submatrix id finSumFinEquiv.symm)ᴴ = p + q
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      fromCols_mul_fromRows_of_nonUnital, ← Matrix.star_eq_conjTranspose,
      ← Matrix.star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
      hp.isIdempotentElem.eq, hq.isIdempotentElem.eq, Matrix.submatrix_id_id]

end Cycle

namespace KZero

variable {A : Type*} [NonUnitalSemiring A] [StarRing A]

/-- **Orthogonal additivity**: `[p + q] = [p] + [q]` when `p * q = 0`. -/
theorem mk_add_of_mul_eq_zero {n : ℕ} {p q : Matrix (Fin n) (Fin n) A}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) :
    mk (⟨n, p + q, hp.add hq hpq⟩ : Cycle A) = mk ⟨n, p, hp⟩ + mk ⟨n, q, hq⟩ := by
  rw [← mk_add]
  exact mk_eq_mk_of_rel (Cycle.rel_of_rectMvN (Cycle.rectMvN_add_of_mul_eq_zero hp hq hpq).symm)

/-- A zero projection of any size has class zero. -/
theorem mk_zero_proj (n : ℕ) : mk (⟨n, 0, IsStarProjection.zero _⟩ : Cycle A) = 0 := by
  rw [mk_eq_mk_of_rel (Cycle.rel_zero_proj n), mk_zero]

end KZero

section Unital

variable {A B : Type*} [Semiring A] [StarRing A] [Semiring B] [StarRing B]

/-- The unit cycle: the `1 × 1` identity matrix. -/
def Cycle.one : Cycle A := ⟨1, 1, IsStarProjection.one _⟩

theorem Cycle.map_one (f : A →⋆ₙ+* B) (hf : f 1 = 1) : (Cycle.one : Cycle A).map f = Cycle.one := by
  show (⟨1, (1 : Matrix (Fin 1) (Fin 1) A).map f, _⟩ : Cycle B) = ⟨1, 1, IsStarProjection.one _⟩
  exact Cycle.eq_of_proj_eq (Matrix.map_one _ (_root_.map_zero f) hf)

variable (A) in
/-- **The unit class** `[1] ∈ K₀(A)`. -/
def KZero.unitClass : KZero A := KZero.mk Cycle.one

/-- A unital `*`-homomorphism preserves the unit class. -/
theorem KZero.map_unitClass (f : A →⋆ₙ+* B) (hf : f 1 = 1) :
    KZero.map f (KZero.unitClass A) = KZero.unitClass B := by
  show KZero.map f (KZero.mk Cycle.one) = KZero.mk Cycle.one
  rw [KZero.map_mk, Cycle.map_one f hf]

end Unital

section Isometry

variable {A : Type*} [Ring A] [StarRing A]

/-- Conjugating a projection by an isometry does not change its stable isomorphism class. -/
theorem Cycle.rel_isometry_conj {n : ℕ} {p u : Matrix (Fin n) (Fin n) A}
    (hp : IsStarProjection p) (hu : star u * u = 1) :
    Cycle.Rel (⟨n, p, hp⟩ : Cycle A)
      ⟨n, u * p * star u, isStarProjection_isometry_conjugate hp hu⟩ :=
  Cycle.rel_of_step (Cycle.Step.mvn (MurrayVonNeumannEquiv.of_isometry_conjugate hp hu))

end Isometry

end KTheory
end GroupApproximation
