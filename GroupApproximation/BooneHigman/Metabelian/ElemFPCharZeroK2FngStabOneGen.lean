import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngTorusOne
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabReduce
import GroupApproximation.Monsters.P13DescentMaster
import GroupApproximation.Meta.AxiomGuard

/-!
# The six unit generators of `St_3(ℤ[1/1])` and the `P13` word map (lane bh-met-92z, 3)

The six `P13` letters `e₁₂, e₁₃, e₂₁, e₂₃, e₃₁, e₃₂` are sent to the Steinberg generators
`x_{pq}(1)` of `St_3(ℤ[1/1])`.  This gives `czK2FngStabOne_F : F₆ →* St_3(ℤ[1/1])`.

* `czK2FngStabOne_padMat_F`: `padMat ∘ F` is the `P13` matrix model `toSL3`, transported
  along `ℤ ≃+* ℤ[1/1]` (`czK2FngStabOne_phi`, which is injective).
* `czK2FngStabOne_F_surjective`: `F` is onto, because `x_{pq}(n) = x_{pq}(1)^n`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

local notation "R₁" => Localization.Away ((1 : ℕ) : ℤ)

/-- Row index of the `P13` letter `g`. -/
def czK2FngStabOne_src (g : Fin 6) : Fin 3 := ![0, 0, 1, 1, 2, 2] g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_src

/-- Column index of the `P13` letter `g`. -/
def czK2FngStabOne_tgt (g : Fin 6) : Fin 3 := ![1, 2, 0, 2, 0, 1] g

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_tgt

theorem czK2FngStabOne_src_ne : ∀ g : Fin 6, czK2FngStabOne_src g ≠ czK2FngStabOne_tgt g := by
  decide

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_src_ne

/-- The `P13` matrix of `g` is `1 + E_{src g, tgt g}`. -/
theorem czK2FngStabOne_elem_eq : ∀ g : Fin 6,
    ((LiteralP13MatrixModel.elem g : LiteralP13MatrixModel.SL3) : Matrix (Fin 3) (Fin 3) ℤ) =
      1 + Matrix.single (czK2FngStabOne_src g) (czK2FngStabOne_tgt g) 1 := by
  decide +kernel

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_elem_eq

/-- Every ordered pair of distinct indices is hit by a letter. -/
theorem czK2FngStabOne_exists_gen : ∀ p q : Fin 3, p ≠ q →
    ∃ g : Fin 6, czK2FngStabOne_src g = p ∧ czK2FngStabOne_tgt g = q := by
  decide

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_exists_gen

/-- The Steinberg generator `x_{src g, tgt g}(1)`. -/
noncomputable def czK2FngStabOne_gen (g : Fin 6) : St 3 R₁ :=
  x (czK2FngStabOne_src g) (czK2FngStabOne_tgt g) (czK2FngStabOne_src_ne g) 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_gen

/-- The word map `F₆ →* St_3(ℤ[1/1])`. -/
noncomputable def czK2FngStabOne_F : FreeGroup (Fin 6) →* St 3 R₁ :=
  FreeGroup.lift czK2FngStabOne_gen

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_F

theorem czK2FngStabOne_F_of (g : Fin 6) :
    czK2FngStabOne_F (FreeGroup.of g) = czK2FngStabOne_gen g := by
  rw [czK2FngStabOne_F, FreeGroup.lift_apply_of]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_F_of

theorem czK2FngStabOne_F_mk (L : List (Fin 6 × Bool)) :
    czK2FngStabOne_F (FreeGroup.mk L) = List.prod (L.map fun a =>
      cond a.2 (czK2FngStabOne_gen a.1) (czK2FngStabOne_gen a.1)⁻¹) := by
  rw [czK2FngStabOne_F, FreeGroup.lift_mk]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_F_mk

/-- Coefficient transport `SL_3(ℤ) →* M_3(ℤ[1/1])`. -/
noncomputable def czK2FngStabOne_phi :
    LiteralP13MatrixModel.SL3 →* Matrix (Fin 3) (Fin 3) R₁ :=
  (RingHom.mapMatrix (m := Fin 3) czK2FngTorus_oneRingEquiv.toRingHom).toMonoidHom.comp
    Matrix.SpecialLinearGroup.coeMonoidHom

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_phi

theorem czK2FngStabOne_phi_apply (A : LiteralP13MatrixModel.SL3) :
    czK2FngStabOne_phi A = (A : Matrix (Fin 3) (Fin 3) ℤ).map czK2FngTorus_oneRingEquiv :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_phi_apply

theorem czK2FngStabOne_phi_injective : Function.Injective czK2FngStabOne_phi := by
  intro A B h
  refine Matrix.SpecialLinearGroup.ext A B fun i j => czK2FngTorus_oneRingEquiv.injective ?_
  have h' : (A : Matrix (Fin 3) (Fin 3) ℤ).map czK2FngTorus_oneRingEquiv i j =
      (B : Matrix (Fin 3) (Fin 3) ℤ).map czK2FngTorus_oneRingEquiv i j := by
    rw [← czK2FngStabOne_phi_apply, ← czK2FngStabOne_phi_apply, h]
  exact h'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_phi_injective

theorem czK2FngStabOne_gen_padMat (g : Fin 6) :
    padMat (czK2FngStabOne_gen g) = czK2FngStabOne_phi (LiteralP13MatrixModel.elem g) := by
  rw [czK2FngStabOne_gen, padMat_x, czK2FngStabOne_phi_apply, czK2FngStabOne_elem_eq,
    Matrix.map_add (⇑czK2FngTorus_oneRingEquiv) (map_add czK2FngTorus_oneRingEquiv),
    Matrix.map_one (⇑czK2FngTorus_oneRingEquiv) (map_zero czK2FngTorus_oneRingEquiv)
      (map_one czK2FngTorus_oneRingEquiv),
    Matrix.map_single, map_one czK2FngTorus_oneRingEquiv]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_gen_padMat

/-- `padMat ∘ F` is the transported `P13` matrix model. -/
theorem czK2FngStabOne_padMat_F (w : FreeGroup (Fin 6)) :
    padMat (czK2FngStabOne_F w) =
      czK2FngStabOne_phi (LiteralP13MatrixModel.toSL3 (LiteralP13Presentation.p13Word w)) := by
  have h : (padMat : St 3 R₁ →* Matrix (Fin 3) (Fin 3) R₁).comp czK2FngStabOne_F =
      czK2FngStabOne_phi.comp
        (LiteralP13MatrixModel.toSL3.comp LiteralP13Presentation.p13Word) := by
    refine FreeGroup.ext_hom _ _ fun g => ?_
    simp only [MonoidHom.comp_apply]
    rw [czK2FngStabOne_F_of, czK2FngStabOne_gen_padMat,
      show LiteralP13Presentation.p13Word (FreeGroup.of g) = PresentedGroup.of g from rfl,
      LiteralP13MatrixModel.toSL3_of]
  exact DFunLike.congr_fun h w

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_padMat_F

/-- `x_{pq}(n)` lies in the image of `F` for every integer `n`. -/
theorem czK2FngStabOne_x_mem_range (p q : Fin 3) (hpq : p ≠ q) (z : ℤ) :
    x p q hpq ((z : ℤ) : R₁) ∈ czK2FngStabOne_F.range := by
  have h1 : x p q hpq 1 ∈ czK2FngStabOne_F.range := by
    obtain ⟨g, rfl, rfl⟩ := czK2FngStabOne_exists_gen p q hpq
    exact MonoidHom.mem_range.mpr ⟨FreeGroup.of g, czK2FngStabOne_F_of g⟩
  induction z using Int.induction_on with
  | zero =>
    rw [Int.cast_zero, x_zero]
    exact one_mem _
  | succ i ih =>
    rw [Int.cast_add, Int.cast_one, ← x_mul]
    exact mul_mem ih h1
  | pred i ih =>
    rw [Int.cast_sub, Int.cast_one, sub_eq_add_neg, ← x_mul, x_neg p q hpq (1 : R₁)]
    exact mul_mem ih (inv_mem h1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_x_mem_range

/-- `F` is onto. -/
theorem czK2FngStabOne_F_surjective (y : St 3 R₁) : y ∈ czK2FngStabOne_F.range := by
  have hsub : Set.range (PresentedGroup.of : SteinbergGenerator (Fin 3) R₁ → St 3 R₁) ⊆
      czK2FngStabOne_F.range := by
    rintro _ ⟨⟨p, q, hpq, a⟩, rfl⟩
    change x p q hpq a ∈ _
    have ha : a = ((czK2FngTorus_oneRingEquiv.symm a : ℤ) : R₁) := by
      rw [← eq_intCast czK2FngTorus_oneRingEquiv, RingEquiv.apply_symm_apply]
    rw [ha]
    exact czK2FngStabOne_x_mem_range p q hpq _
  exact (Subgroup.closure_le czK2FngStabOne_F.range).mpr hsub (mem_closure_range_of y)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_F_surjective

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
