import GroupApproximation.Kazhdan.KazhdanOrthogonal
import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.Analysis.Real.Hyperreal

/-!
# Finite permutation representations

This module turns an exact action on a finite set into its canonical
orthogonal representation on the real square-summable functions.  It is the
finite-dimensional representation used in the spectral part of Kun's
expander-decomposition argument.
-/

namespace GroupApproximation
namespace KazhdanFiniteModel

open scoped symmDiff
open KazhdanOrthogonal

universe u v

variable {G : Type u} [Group G]
variable {Y : Type v} [Fintype Y]

section SoficNormalization

variable {M : FiniteModel}

/-- Taking a hyperreal class of a real sequence, bundled as a ring
homomorphism. -/
noncomputable def ofSeqRingHom : (ℕ → ℝ) →+* Hyperreal :=
  { toFun := Hyperreal.ofSeq
    map_zero' := rfl
    map_one' := rfl
    map_add' := fun _ _ ↦ rfl
    map_mul' := fun _ _ ↦ rfl }

/-- A real number embedded in the hyperreals is finite. -/
theorem hyperreal_coe_finite (r : ℝ) :
    0 ≤ ArchimedeanClass.mk (r : Hyperreal) := by
  apply ArchimedeanClass.mk_nonneg_of_le_of_le_of_archimedean
    Hyperreal.coeRingHom (r := r - 1) (s := r + 1)
  · simp
  · simp

/-- Finite hyperreals are closed under addition. -/
theorem hyperreal_add_finite {x y : Hyperreal}
    (hx : 0 ≤ ArchimedeanClass.mk x)
    (hy : 0 ≤ ArchimedeanClass.mk y) :
    0 ≤ ArchimedeanClass.mk (x + y) :=
  (le_min hx hy).trans (ArchimedeanClass.min_le_mk_add x y)

/-- Finite hyperreals are closed under multiplication. -/
theorem hyperreal_mul_finite {x y : Hyperreal}
    (hx : 0 ≤ ArchimedeanClass.mk x)
    (hy : 0 ≤ ArchimedeanClass.mk y) :
    0 ≤ ArchimedeanClass.mk (x * y) := by
  rw [ArchimedeanClass.mk_mul]
  exact add_nonneg hx hy

/-- A finite sum of finite hyperreals is finite. -/
theorem hyperreal_finset_sum_finite {I : Type*} (F : Finset I)
    (x : I → Hyperreal)
    (hx : ∀ i ∈ F, 0 ≤ ArchimedeanClass.mk (x i)) :
    0 ≤ ArchimedeanClass.mk (∑ i ∈ F, x i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
      rw [Finset.sum_insert ha]
      exact hyperreal_add_finite (hx a (by simp))
        (ih fun i hi ↦ hx i (by simp [hi]))

/-- Standard part commutes with a finite sum of finite hyperreals. -/
theorem stdPart_finset_sum {I : Type*} (F : Finset I)
    (x : I → Hyperreal)
    (hx : ∀ i ∈ F, 0 ≤ ArchimedeanClass.mk (x i)) :
    ArchimedeanClass.stdPart (∑ i ∈ F, x i) =
      ∑ i ∈ F, ArchimedeanClass.stdPart (x i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        ArchimedeanClass.stdPart_add (hx a (by simp))
          (hyperreal_finset_sum_finite F x fun i hi ↦ hx i (by simp [hi])),
        ih fun i hi ↦ hx i (by simp [hi])]

/-- Standard positive-definiteness for a real-valued function on a group,
expressed using all finite real quadratic forms. -/
def IsPositiveDefinite (f : G → ℝ) : Prop :=
  (∀ g h : G, f (g⁻¹ * h) = f (h⁻¹ * g)) ∧
    ∀ (F : Finset G) (c : G → ℝ),
      0 ≤ ∑ i ∈ F, ∑ j ∈ F, c i * c j * f (i⁻¹ * j)

end SoficNormalization

end KazhdanFiniteModel
end GroupApproximation
