import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Doubling in `ℤ³ ⋊ SL₃(ℤ)`

This is the concrete affine group and endomorphism from manuscript Lemma
`lem:alpha`.  It is deliberately independent of the six-generator
presentation: the linear factor is mathlib's actual special linear group and
the translation factor is the actual lattice `Fin 3 → ℤ`.
-/

namespace GroupApproximation
namespace AffineSL3Doubling

open Matrix
open scoped MatrixGroups

abbrev Lattice := Fin 3 → ℤ
abbrev Linear := SL(3, ℤ)

/-- The standard `SL₃(ℤ)` action on the multiplicative copy of `ℤ³`. -/
def action : Linear →* MulAut (Multiplicative Lattice) :=
  (MulAutMultiplicative Lattice).symm.toMonoidHom.comp
    (DistribMulAction.toAddAut Linear Lattice)

/-- The concrete affine semidirect product `ℤ³ ⋊ SL₃(ℤ)`. -/
abbrev Gamma := SemidirectProduct (Multiplicative Lattice) Linear action

/-- Doubling on the additive lattice. -/
def doubleAdd : Lattice →+ Lattice where
  toFun v := 2 • v
  map_zero' := by simp
  map_add' _ _ := by module

/-- Doubling on the multiplicative copy used by the semidirect product. -/
def doubleMul : Multiplicative Lattice →* Multiplicative Lattice :=
  doubleAdd.toMultiplicative

theorem doubleMul_injective : Function.Injective doubleMul := by
  intro v w h
  change v.toAdd = w.toAdd
  change 2 • v.toAdd = 2 • w.toAdd at h
  ext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, nsmul_eq_mul] at hi
  omega

theorem doubleMul_commutes_action (A : Linear) :
    doubleMul.comp (action A).toMonoidHom =
      (action A).toMonoidHom.comp doubleMul := by
  apply MonoidHom.ext
  intro v
  change 2 • (A • v.toAdd) = A • (2 • v.toAdd)
  exact (map_nsmul (DistribMulAction.toAddAut Linear Lattice A).toAdd
    2 v.toAdd).symm

/-- The manuscript endomorphism `α(v,A) = (2v,A)`. -/
def alpha : Gamma →* Gamma :=
  SemidirectProduct.map doubleMul (MonoidHom.id Linear)
    doubleMul_commutes_action

@[simp] theorem alpha_left (g : Gamma) :
    (alpha g).left = doubleMul g.left := rfl

@[simp] theorem alpha_right (g : Gamma) :
    (alpha g).right = g.right := rfl

theorem alpha_injective : Function.Injective alpha := by
  intro g h heq
  apply SemidirectProduct.ext
  · exact doubleMul_injective (congrArg SemidirectProduct.left heq)
  · simpa only [alpha_right] using congrArg SemidirectProduct.right heq

/-- The first standard translation `(e₁,1)`. -/
def aVector : Lattice := Pi.single 0 1

def a : Gamma :=
  ⟨Multiplicative.ofAdd aVector, 1⟩

theorem aVector_zero : aVector 0 = 1 := by
  simp [aVector]

/-- The marked first translation is not in the doubled image. -/
theorem a_not_mem_range : a ∉ Set.range alpha := by
  rintro ⟨g, hg⟩
  have hleft := congrArg SemidirectProduct.left hg
  change 2 • g.left.toAdd = aVector at hleft
  have hzero := congrFun hleft 0
  simp only [Pi.smul_apply, nsmul_eq_mul, aVector_zero] at hzero
  omega

/-- Exact description of the image: its translation coordinate is even and
its `SL₃(ℤ)` coordinate is arbitrary. -/
theorem mem_range_alpha_iff (g : Gamma) :
    g ∈ Set.range alpha ↔ ∃ v : Lattice, g.left.toAdd = 2 • v := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h.left.toAdd, rfl⟩
  · rintro ⟨v, hv⟩
    let h : Gamma := ⟨Multiplicative.ofAdd v, g.right⟩
    refine ⟨h, SemidirectProduct.ext ?_ ?_⟩
    · change 2 • v = g.left.toAdd
      exact hv.symm
    · rfl

/-- The endomorphism and escaping-vector part of manuscript Lemma
`lem:alpha`. -/
theorem doubling_package :
    Function.Injective alpha ∧
      (∀ g : Gamma,
        g ∈ Set.range alpha ↔ ∃ v : Lattice, g.left.toAdd = 2 • v) ∧
      a ∉ Set.range alpha :=
  ⟨alpha_injective, mem_range_alpha_iff, a_not_mem_range⟩

end AffineSL3Doubling
end GroupApproximation
