import GroupApproximation.Leavitt.FiniteModuleObstruction
import GroupApproximation.Leavitt.UnitAdditiveSpan
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Finite dual orbits over a binary Leavitt ring are trivial

A finite family of additive characters which is closed under left translation
by every unit has a common kernel.  The unit-span theorem makes that common
kernel a left ideal.  Its quotient injects into a finite function space, so
the finite-module obstruction forces the quotient, and hence every character
in the family, to be trivial.
-/

namespace GroupApproximation
namespace LeavittFamily

variable {A : Type*} [Ring A]

/-- Additive left multiplication by a fixed ring element. -/
def leftMulAddHom (a : A) : A →+ A where
  toFun x := a * x
  map_zero' := mul_zero a
  map_add' x y := mul_add a x y

/-- Simultaneous evaluation on a finite family of additive characters. -/
def finiteEvaluation (O : Finset (A →+ ZMod 2)) :
    A →+ ((f : ↑O) → ZMod 2) where
  toFun a f := f.1 a
  map_zero' := by
    funext f
    exact f.1.map_zero
  map_add' x y := by
    funext f
    exact f.1.map_add x y

/-- The common kernel of a finite unit-translation-invariant family is a
left ideal, presented as a submodule of the left regular module. -/
def finiteOrbitKernel (L : LeavittFamily A) (O : Finset (A →+ ZMod 2))
    (hstable : ∀ (f : A →+ ZMod 2), f ∈ O → ∀ u : Aˣ,
      f.comp (leftMulAddHom (u : A)) ∈ O) : Submodule A A where
  carrier := (finiteEvaluation O).ker
  zero_mem' := (finiteEvaluation O).ker.zero_mem
  add_mem' := (finiteEvaluation O).ker.add_mem
  smul_mem' := by
    intro r a ha
    let S : AddSubgroup A :=
      { carrier := {x | ∀ y, y ∈ (finiteEvaluation O).ker →
            x * y ∈ (finiteEvaluation O).ker}
        zero_mem' := by simp
        add_mem' := by
          intro x y hx hy z hz
          simpa [add_mul] using (finiteEvaluation O).ker.add_mem (hx z hz) (hy z hz)
        neg_mem' := by
          intro x hx y hy
          simpa [neg_mul] using (finiteEvaluation O).ker.neg_mem (hx y hy) }
    have hunit : ∀ u : Aˣ, (u : A) ∈ S := by
      intro u y hy
      rw [AddMonoidHom.mem_ker] at hy ⊢
      funext f
      have htranslated : f.1.comp (leftMulAddHom (u : A)) ∈ O :=
        hstable f.1 f.2 u
      have hzero := congrFun hy
        (⟨f.1.comp (leftMulAddHom (u : A)), htranslated⟩ : ↑O)
      exact hzero
    have hspan : unitAdditiveSpan A ≤ S := by
      apply (AddSubgroup.closure_le S).2
      rintro _ ⟨u, rfl⟩
      exact hunit u
    have hr : r ∈ unitAdditiveSpan A := by
      rw [L.unitAdditiveSpan_eq_top]
      trivial
    exact hspan hr a ha

/-- A finite family of additive `F₂`-characters which is invariant under
all left-unit translates consists only of the zero character. -/
theorem finite_unit_translate_family_eq_zero (L : LeavittFamily A)
    (O : Finset (A →+ ZMod 2))
    (hstable : ∀ (f : A →+ ZMod 2), f ∈ O → ∀ u : Aˣ,
      f.comp (leftMulAddHom (u : A)) ∈ O)
    {f : A →+ ZMod 2} (hf : f ∈ O) : f = 0 := by
  let N : Submodule A A := finiteOrbitKernel L O hstable
  let e : (A ⧸ N) ≃+ AddMonoidHom.range (finiteEvaluation O) := by
    change (A ⧸ (finiteEvaluation O).ker) ≃+
      AddMonoidHom.range (finiteEvaluation O)
    exact QuotientAddGroup.quotientKerEquivRange (finiteEvaluation O)
  letI : Finite (AddMonoidHom.range (finiteEvaluation O)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (A ⧸ N) := Finite.of_injective e e.injective
  letI : Fintype (A ⧸ N) := Fintype.ofFinite (A ⧸ N)
  have hsub : Subsingleton (A ⧸ N) := L.finite_module_subsingleton
  apply AddMonoidHom.ext
  intro a
  have hquot : (Submodule.Quotient.mk a : A ⧸ N) = 0 := hsub.elim _ _
  have haN : a ∈ N := Submodule.Quotient.mk_eq_zero N |>.mp hquot
  change a ∈ (finiteEvaluation O).ker at haN
  rw [AddMonoidHom.mem_ker] at haN
  exact congrFun haN ⟨f, hf⟩

end LeavittFamily
end GroupApproximation
