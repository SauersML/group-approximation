import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.CoprodI
import Mathlib.Algebra.Group.ULift

/-!
# Reduced normal forms for the binary free product `G ∗ ℤ`

Mathlib supplies reduced words for `Monoid.CoprodI`, but its separately
implemented binary `Monoid.Coprod` has no normal-form API.  For the free
product used by the Bass--Serre pivot, we bridge the two universal properties
explicitly.  The right factor is universe-lifted so both indexed factors live
  in the universe of `G`.
-/

namespace GroupApproximation
namespace BinaryCoprodNormalForm

open Monoid Monoid.CoprodI

universe u

variable (G : Type u) [Group G]

/-- The two factors, in one universe. -/
def factor : Bool → Type u
  | false => G
  | true => ULift.{u} (Multiplicative ℤ)

instance factorGroup (i : Bool) : Group (factor G i) := by
  cases i <;> simp only [factor] <;> infer_instance

/-- The binary free product maps to the indexed free product of the same two
factors. -/
def toIndexed :
    Monoid.Coprod G (Multiplicative ℤ) →* CoprodI (factor G) :=
  Monoid.Coprod.lift
    (CoprodI.of (M := factor G) (i := false))
    ((CoprodI.of (M := factor G) (i := true)).comp
      MulEquiv.ulift.symm.toMonoidHom)

/-- The inverse map, defined by the indexed universal property. -/
def fromIndexed :
    CoprodI (factor G) →* Monoid.Coprod G (Multiplicative ℤ) :=
  CoprodI.lift fun i ↦ by
    cases i with
    | false =>
        exact (Monoid.Coprod.inl : G →* Monoid.Coprod G (Multiplicative ℤ))
    | true =>
        exact (Monoid.Coprod.inr : Multiplicative ℤ →*
          Monoid.Coprod G (Multiplicative ℤ)).comp
            MulEquiv.ulift.toMonoidHom

@[simp] theorem toIndexed_inl (g : G) :
    toIndexed G (Monoid.Coprod.inl g) = CoprodI.of (i := false) g := by
  simp [toIndexed] <;> rfl

@[simp] theorem toIndexed_inr (z : Multiplicative ℤ) :
    toIndexed G (Monoid.Coprod.inr z) =
      CoprodI.of (i := true) (MulEquiv.ulift.symm z) := by
  simp [toIndexed] <;> rfl

@[simp] theorem fromIndexed_of_false (g : G) :
    fromIndexed G (CoprodI.of (i := false) g) = Monoid.Coprod.inl g := by
  simp [fromIndexed] <;> rfl

@[simp] theorem fromIndexed_of_true (z : ULift.{u} (Multiplicative ℤ)) :
    fromIndexed G (CoprodI.of (i := true) z) =
      Monoid.Coprod.inr (MulEquiv.ulift z) := by
  simp [fromIndexed] <;> rfl

theorem fromIndexed_comp_toIndexed :
    (fromIndexed G).comp (toIndexed G) = MonoidHom.id _ := by
  apply Monoid.Coprod.hom_ext
  · ext g
    simp
  · ext z
    simp

theorem toIndexed_comp_fromIndexed :
    (toIndexed G).comp (fromIndexed G) = MonoidHom.id _ := by
  apply CoprodI.ext_hom
  intro i
  cases i with
  | false =>
      ext g
      simp
  | true =>
      ext z
      simp

/-- The binary and indexed free products are canonically isomorphic. -/
def binaryEquivIndexed :
    Monoid.Coprod G (Multiplicative ℤ) ≃*
      CoprodI (factor G) :=
  MonoidHom.toMulEquiv (toIndexed G) (fromIndexed G)
    (fromIndexed_comp_toIndexed G) (toIndexed_comp_fromIndexed G)

/-- The reduced alternating normal form of a binary-free-product element. -/
noncomputable def normalForm (g : Monoid.Coprod G (Multiplicative ℤ)) :
    CoprodI.Word (factor G) := by
  classical
  exact CoprodI.Word.equiv (toIndexed G g)

/-- Multiplying the normal form recovers the element after transport to the
indexed free product. -/
theorem normalForm_prod (g : Monoid.Coprod G (Multiplicative ℤ)) :
    (normalForm G g).prod = toIndexed G g := by
  classical
  change (CoprodI.Word.equiv (toIndexed G g)).prod = toIndexed G g
  exact CoprodI.Word.equiv.symm_apply_apply (toIndexed G g)

/-- **Uniqueness at the identity:** the reduced normal form is empty exactly
for the identity element. -/
theorem normalForm_eq_empty_iff
    (g : Monoid.Coprod G (Multiplicative ℤ)) :
    normalForm G g = CoprodI.Word.empty ↔ g = 1 := by
  classical
  constructor
  · intro h
    apply (binaryEquivIndexed G).injective
    change toIndexed G g = toIndexed G 1
    rw [← normalForm_prod G g, h]
    simp
  · rintro rfl
    apply CoprodI.Word.equiv.symm.injective
    change (normalForm G 1).prod = CoprodI.Word.empty.prod
    rw [normalForm_prod]
    simp

/-- **No nonempty reduced normal form represents the identity.** -/
theorem ne_one_of_normalForm_toList_ne_nil
    {g : Monoid.Coprod G (Multiplicative ℤ)}
    (h : (normalForm G g).toList ≠ []) : g ≠ 1 := by
  intro hg
  apply h
  have hempty := (normalForm_eq_empty_iff G g).2 hg
  rw [hempty]
  rfl

/-- Equality in the binary free product is equality of reduced normal forms. -/
theorem normalForm_injective : Function.Injective (normalForm G) := by
  classical
  intro x y h
  apply (binaryEquivIndexed G).injective
  change toIndexed G x = toIndexed G y
  rw [← normalForm_prod G x, ← normalForm_prod G y, h]

/-- An arbitrary indexed reduced word, transported back to the binary free
product, represents `1` exactly when it is empty. -/
theorem fromIndexed_prod_eq_one_iff
    (w : CoprodI.Word (factor G)) :
    fromIndexed G w.prod = 1 ↔ w = CoprodI.Word.empty := by
  classical
  constructor
  · intro h
    apply CoprodI.Word.equiv.symm.injective
    change w.prod = CoprodI.Word.empty.prod
    calc
      w.prod = toIndexed G (fromIndexed G w.prod) := by
        have hc := DFunLike.congr_fun (toIndexed_comp_fromIndexed G) w.prod
        exact hc.symm
      _ = toIndexed G 1 := congrArg (toIndexed G) h
      _ = CoprodI.Word.empty.prod := by simp
  · rintro rfl
    simp

/-- **A nonempty reduced alternating word in the two factors is nontrivial in
the binary coproduct.** -/
theorem fromIndexed_prod_ne_one_of_toList_ne_nil
    {w : CoprodI.Word (factor G)} (hw : w.toList ≠ []) :
    fromIndexed G w.prod ≠ 1 := by
  intro h
  have hempty := (fromIndexed_prod_eq_one_iff G w).mp h
  apply hw
  rw [hempty]
  rfl

end BinaryCoprodNormalForm
end GroupApproximation
