import GroupApproximation.Leavitt.ElementaryRoots
import GroupApproximation.Leavitt.UniversalLeavittOver

/-!
# The binary Leavitt shift

Every binary Leavitt family carries the proper injective endomorphism

`a ↦ s₀ a t₀ + s₁ a t₁`.

For the universal binary Leavitt algebra this induces a proper self-embedding
of its rank-four elementary group.  Iterating the image therefore gives the
strict descending chain of copies used to identify the explicit simple
nonsofic witness as an `omega`-nonsofic group.
-/

namespace GroupApproximation

namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

private theorem sandwich_mul (s t u v a b : A) :
    (s * a * t) * (u * b * v) = s * (a * (t * u) * b) * v := by
  noncomm_ring

/-- The canonical binary shift associated to a Leavitt family. -/
def shift : A →+* A where
  toFun a := L.s0 * a * L.t0 + L.s1 * a * L.t1
  map_zero' := by simp
  map_one' := by simpa using L.sum_range
  map_add' a b := by noncomm_ring
  map_mul' a b := by
    rw [mul_add, add_mul, add_mul]
    simp_rw [sandwich_mul]
    rw [L.t0_s0, L.t0_s1, L.t1_s0, L.t1_s1]
    simp

@[simp] theorem shift_apply (a : A) :
    L.shift a = L.s0 * a * L.t0 + L.s1 * a * L.t1 := rfl

/-- The zero cylinder is a left inverse for the binary shift. -/
@[simp] theorem t0_mul_shift_mul_s0 (a : A) :
    L.t0 * L.shift a * L.s0 = a := by
  rw [shift_apply, mul_add, add_mul]
  calc
    L.t0 * (L.s0 * a * L.t0) * L.s0 +
        L.t0 * (L.s1 * a * L.t1) * L.s0 =
      (L.t0 * L.s0) * a * (L.t0 * L.s0) +
        (L.t0 * L.s1) * a * (L.t1 * L.s0) := by noncomm_ring
    _ = a := by rw [L.t0_s0, L.t0_s1, L.t1_s0]; simp

/-- Distinct cylinders detect that the shift misses a generator. -/
@[simp] theorem t0_mul_shift_mul_s1 (a : A) :
    L.t0 * L.shift a * L.s1 = 0 := by
  rw [shift_apply, mul_add, add_mul]
  calc
    L.t0 * (L.s0 * a * L.t0) * L.s1 +
        L.t0 * (L.s1 * a * L.t1) * L.s1 =
      (L.t0 * L.s0) * a * (L.t0 * L.s1) +
        (L.t0 * L.s1) * a * (L.t1 * L.s1) := by noncomm_ring
    _ = 0 := by rw [L.t0_s0, L.t0_s1, L.t1_s1]; simp

theorem shift_injective : Function.Injective L.shift := by
  intro a b hab
  have h := congrArg (fun z : A ↦ L.t0 * z * L.s0) hab
  simpa only [L.t0_mul_shift_mul_s0] using h

theorem s1_ne_zero [Nontrivial A] : L.s1 ≠ 0 := by
  intro hs
  have h := L.t1_s1
  rw [hs, mul_zero] at h
  exact zero_ne_one h

/-- The binary shift is proper; `s₀` is an explicit omitted element. -/
theorem s0_not_mem_shift_range [Nontrivial A] : L.s0 ∉ Set.range L.shift := by
  rintro ⟨a, ha⟩
  have h := congrArg (fun z : A ↦ L.t0 * z * L.s1) ha
  have hs : L.s1 = 0 := by
    simpa only [L.t0_mul_shift_mul_s1, L.t0_s0, one_mul] using h.symm
  exact L.s1_ne_zero hs

theorem shift_not_surjective [Nontrivial A] :
    ¬ Function.Surjective L.shift := by
  intro h
  exact L.s0_not_mem_shift_range (h L.s0)

end LeavittFamily

namespace BinaryLeavitt

open LeavittFamily

variable (k : Type*) [Field k]

/-- The binary shift induces an injective endomorphism of `EL₄`. -/
def elementaryShift :
    elementaryGroup (Fin 4) (BinaryLeavittAlgebra k) →*
      elementaryGroup (Fin 4) (BinaryLeavittAlgebra k) :=
  elementaryGroupMap (family k).shift

theorem elementaryShift_injective :
    Function.Injective (elementaryShift k) := by
  intro x y h
  apply Subtype.ext
  apply Units.map_injective (f := (family k).shift.mapMatrix.toMonoidHom)
    (fun M N hMN => Matrix.ext fun i j => (family k).shift_injective (by
      have hentry := congrArg
        (fun X : Matrix (Fin 4) (Fin 4) (BinaryLeavittAlgebra k) => X i j) hMN
      simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using hentry))
  exact congrArg
    (fun z : elementaryGroup (Fin 4) (BinaryLeavittAlgebra k) =>
      (z : (Matrix (Fin 4) (Fin 4) (BinaryLeavittAlgebra k))ˣ)) h

/-- The elementary transvection with coefficient `s₀` is not in the image of
the induced shift. -/
theorem elementaryRoot_s0_not_mem_shift_range :
    elementaryRoot (R := BinaryLeavittAlgebra k) (0 : Fin 4) (1 : Fin 4)
        (by decide) (family k).s0 ∉ Set.range (elementaryShift k) := by
  rintro ⟨g, hg⟩
  have h := congrArg
    (fun z : elementaryGroup (Fin 4) (BinaryLeavittAlgebra k) =>
      (((z : (Matrix (Fin 4) (Fin 4) (BinaryLeavittAlgebra k))ˣ) :
        Matrix (Fin 4) (Fin 4) (BinaryLeavittAlgebra k)) 0 1)) hg
  have hrange : (family k).s0 ∈ Set.range (family k).shift := by
    refine ⟨(((g : (Matrix (Fin 4) (Fin 4) (BinaryLeavittAlgebra k))ˣ) :
      Matrix (Fin 4) (Fin 4) (BinaryLeavittAlgebra k)) 0 1), ?_⟩
    simpa [elementaryShift, elementaryGroupMap_apply,
      elementaryMatrixUnitMap, RingHom.mapMatrix_apply, Matrix.map_apply,
      elementaryRoot, elementaryUnit] using h
  exact (family k).s0_not_mem_shift_range hrange

theorem elementaryShift_not_surjective :
    ¬ Function.Surjective (elementaryShift k) := by
  intro h
  exact elementaryRoot_s0_not_mem_shift_range k
    (h (elementaryRoot (R := BinaryLeavittAlgebra k) (0 : Fin 4) (1 : Fin 4)
      (by decide) (family k).s0))

end BinaryLeavitt

end GroupApproximation
