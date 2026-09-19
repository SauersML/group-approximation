import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.IndexNSmul
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
  toFun := nsmulAddMonoidHom 2
  map_zero' := map_zero (nsmulAddMonoidHom 2)
  map_add' := map_add (nsmulAddMonoidHom 2)

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

/-- The doubled lattice has index `2³ = 8`. -/
theorem doubleMul_range_index : doubleMul.range.index = 8 := by
  change (AddSubgroup.toSubgroup
    (nsmulAddMonoidHom (α := Lattice) 2).range).index = 8
  rw [AddSubgroup.index_toSubgroup, AddSubgroup.index_range_nsmul]
  norm_num

abbrev DoubleCosets := (Multiplicative Lattice) ⧸ doubleMul.range
abbrev AlphaCosets := Gamma ⧸ alpha.range

/-- Inclusion of the translation subgroup induces the map from doubled
lattice cosets to affine doubled-image cosets. -/
def cosetMap : DoubleCosets → AlphaCosets :=
  Quotient.map' SemidirectProduct.inl (by
    intro x y hxy
    apply QuotientGroup.leftRel_apply.mpr
    rw [QuotientGroup.leftRel_apply] at hxy
    rcases hxy with ⟨z, hz⟩
    refine ⟨SemidirectProduct.inl z, ?_⟩
    apply SemidirectProduct.ext
    · simpa [alpha] using hz
    · simp)

theorem cosetMap_injective : Function.Injective cosetMap := by
  refine Quotient.ind' (fun x ↦ Quotient.ind' (fun y hxy ↦ ?_))
  apply Quotient.sound'
  apply QuotientGroup.leftRel_apply.mpr
  have htarget : QuotientGroup.leftRel alpha.range
      (SemidirectProduct.inl x) (SemidirectProduct.inl y) := by
    exact Quotient.exact' hxy
  rw [QuotientGroup.leftRel_apply] at htarget
  rcases htarget with ⟨g, hg⟩
  refine ⟨g.left, ?_⟩
  simpa [alpha] using congrArg SemidirectProduct.left hg

theorem cosetMap_surjective : Function.Surjective cosetMap := by
  refine Quotient.ind' (fun g ↦ ?_)
  refine ⟨Quotient.mk'' g.left, ?_⟩
  rw [cosetMap, Quotient.map'_mk'']
  apply Quotient.sound'
  apply QuotientGroup.leftRel_apply.mpr
  have hsplit : (SemidirectProduct.inl g.left)⁻¹ * g =
      SemidirectProduct.inr g.right := by
    apply SemidirectProduct.ext <;> simp
  rw [hsplit]
  refine ⟨SemidirectProduct.inr g.right, ?_⟩
  apply SemidirectProduct.ext <;> simp [alpha]

/-- Cosets of the affine doubled image are exactly parity classes in the
translation lattice. -/
noncomputable def cosetEquiv : DoubleCosets ≃ AlphaCosets :=
  Equiv.ofBijective cosetMap ⟨cosetMap_injective, cosetMap_surjective⟩

/-- The image of `α` has index eight in the affine group. -/
theorem alpha_range_index : alpha.range.index = 8 := by
  rw [Subgroup.index_eq_card, ← Nat.card_congr cosetEquiv,
    ← Subgroup.index_eq_card]
  exact doubleMul_range_index

/-- The endomorphism and escaping-vector part of manuscript Lemma
`lem:alpha`. -/
theorem doubling_package :
    Function.Injective alpha ∧
      (∀ g : Gamma,
        g ∈ Set.range alpha ↔ ∃ v : Lattice, g.left.toAdd = 2 • v) ∧
      alpha.range.index = 8 ∧
      a ∉ Set.range alpha :=
  ⟨alpha_injective, mem_range_alpha_iff, alpha_range_index, a_not_mem_range⟩

end AffineSL3Doubling
end GroupApproximation
