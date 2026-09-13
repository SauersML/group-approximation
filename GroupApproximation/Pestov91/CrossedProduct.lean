import Mathlib.Algebra.SkewMonoidAlgebra.Basic
import Mathlib.Algebra.Group.Int.TypeTags

/-!
# The crossed product `A ⋊ ℤ`

Pestov's Open Question 9.1 (*Hyperlinear and sofic groups: a brief guide*, arXiv:0804.3968v8,
p. 21) is answered by `S = EL₃(R)/Z(EL₃(R))` with `R = LC(X, 𝔽_q) ⋊ ℤ`, for an infinite minimal
subshift `X`.  The crossed product `A ⋊ ℤ` of a ring `A` by an action of `ℤ` is realised here as
Mathlib's skew monoid algebra

  `SkewMonoidAlgebra A (Multiplicative ℤ)`,  over `[MulSemiringAction (Multiplicative ℤ) A]`.

Its elements are the finitely supported functions `ℤ → A`, and
`single m a * single n b = single (m * n) (a * m • b)`.  This is the algebraic crossed product
itself, with its unique normal form, so no quotient and no representation is involved.

This module fixes the interface of the ring for the other Pestov 9.1 modules, for an arbitrary
action of `ℤ`:

* `C : A →+* A ⋊ ℤ` is the coefficient embedding `a ↦ single 1 a`;
* `unit` is the implementing unit `u = single (ofAdd 1) 1`, and
  `val_unit_zpow : ↑(u ^ j) = single (ofAdd j) 1`;
* `unit_zpow_mul_C : ↑(u ^ j) * C a = C (ofAdd j • a) * ↑(u ^ j)` is the covariance relation;
* `exists_sum_C_mul_unit_zpow`: every element is a finite sum `∑ j ∈ S, C (c j) * ↑(u ^ j)`.
-/

namespace GroupApproximation
namespace Pestov91
namespace CrossedProduct

open SkewMonoidAlgebra (single)
open Multiplicative (ofAdd toAdd)

variable {A : Type*} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]

/-- The coefficient embedding `A →+* A ⋊ ℤ`, `a ↦ single 1 a`. -/
noncomputable def C : A →+* SkewMonoidAlgebra A (Multiplicative ℤ) :=
  SkewMonoidAlgebra.singleOneRingHom

theorem C_apply (a : A) : C a = single (1 : Multiplicative ℤ) a :=
  rfl

@[simp]
theorem C_mul_single (a b : A) (g : Multiplicative ℤ) :
    C a * single g b = single g (a * b) := by
  rw [C_apply, SkewMonoidAlgebra.single_mul_single, one_mul, one_smul]

theorem single_mul_C (g : Multiplicative ℤ) (a b : A) :
    single g b * C a = single g (b * g • a) := by
  rw [C_apply, SkewMonoidAlgebra.single_mul_single, mul_one]

/-- Every monomial is a coefficient times `single g 1`. -/
theorem single_eq_C_mul (g : Multiplicative ℤ) (a : A) :
    single g a = C a * single g (1 : A) := by
  rw [C_mul_single, mul_one]

/-! ### The implementing unit -/

/-- `single g 1` is a unit, with inverse `single g⁻¹ 1`. -/
noncomputable def unitOf (g : Multiplicative ℤ) : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ where
  val := single g 1
  inv := single g⁻¹ 1
  val_inv := by
    rw [SkewMonoidAlgebra.single_mul_single, smul_one, mul_one, mul_inv_cancel,
      SkewMonoidAlgebra.single_one_one]
  inv_val := by
    rw [SkewMonoidAlgebra.single_mul_single, smul_one, mul_one, inv_mul_cancel,
      SkewMonoidAlgebra.single_one_one]

@[simp]
theorem val_unitOf (g : Multiplicative ℤ) :
    ((unitOf g : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) :
      SkewMonoidAlgebra A (Multiplicative ℤ)) = single g 1 :=
  rfl

@[simp]
theorem val_inv_unitOf (g : Multiplicative ℤ) :
    (((unitOf g)⁻¹ : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) :
      SkewMonoidAlgebra A (Multiplicative ℤ)) = single g⁻¹ 1 :=
  rfl

theorem unitOf_mul (g h : Multiplicative ℤ) :
    (unitOf (g * h) : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) = unitOf g * unitOf h :=
  Units.ext <| by
    simp only [Units.val_mul, val_unitOf, SkewMonoidAlgebra.single_mul_single, smul_one, mul_one]

/-- `g ↦ single g 1`, as a homomorphism from `ℤ` into the units of `A ⋊ ℤ`. -/
noncomputable def unitHom : Multiplicative ℤ →* (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ where
  toFun := unitOf
  map_one' := Units.ext <| by
    simp only [val_unitOf, Units.val_one, SkewMonoidAlgebra.single_one_one]
  map_mul' := unitOf_mul

@[simp]
theorem unitHom_apply (g : Multiplicative ℤ) :
    (unitHom g : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) = unitOf g :=
  rfl

/-- The implementing unit `u = single (ofAdd 1) 1` of `A ⋊ ℤ`. -/
noncomputable def unit : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ :=
  unitOf (ofAdd 1)

theorem unit_zpow (j : ℤ) :
    (unit : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) ^ j = unitOf (ofAdd j) := by
  have h : (ofAdd (1 : ℤ)) ^ j = ofAdd j := by
    rw [← Int.ofAdd_mul, one_mul]
  have h' := map_zpow
    (unitHom : Multiplicative ℤ →* (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) (ofAdd 1) j
  rw [h] at h'
  exact h'.symm

theorem val_unit_zpow (j : ℤ) :
    (((unit : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) ^ j :
      (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) : SkewMonoidAlgebra A (Multiplicative ℤ)) =
      single (ofAdd j) 1 := by
  rw [unit_zpow, val_unitOf]

/-- **Covariance.**  Conjugation by `u ^ j` implements the action of `j`:
`u ^ j * C a = C (ofAdd j • a) * u ^ j`. -/
theorem unit_zpow_mul_C (j : ℤ) (a : A) :
    ((unit ^ j : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) :
      SkewMonoidAlgebra A (Multiplicative ℤ)) * C a =
      C (ofAdd j • a) * ((unit ^ j : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) :
        SkewMonoidAlgebra A (Multiplicative ℤ)) := by
  rw [val_unit_zpow, single_mul_C, C_mul_single, one_mul, mul_one]

/-- **Normal form.**  Every element of `A ⋊ ℤ` is a finite sum `∑ j ∈ S, C (c j) * ↑(u ^ j)`. -/
theorem exists_sum_C_mul_unit_zpow (x : SkewMonoidAlgebra A (Multiplicative ℤ)) :
    ∃ (S : Finset ℤ) (c : ℤ → A),
      x = ∑ j ∈ S, C (c j) * ((unit ^ j : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) :
        SkewMonoidAlgebra A (Multiplicative ℤ)) := by
  refine ⟨x.support.map toAdd.toEmbedding, fun j => x.coeff (ofAdd j), ?_⟩
  calc x = x.sum single := (SkewMonoidAlgebra.sum_single x).symm
    _ = ∑ g ∈ x.support, single g (x.coeff g) := SkewMonoidAlgebra.sum_def' _ _
    _ = _ := by simp [Finset.sum_map, val_unit_zpow]

end CrossedProduct
end Pestov91
end GroupApproximation
