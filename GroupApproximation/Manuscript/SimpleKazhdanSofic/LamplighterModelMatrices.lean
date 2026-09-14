import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterModelAction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LamplighterRing
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# The matrices `D_n(f)`, `P_ξ` and the maps `φ_n`

`simple_kazhdan_sofic_group.tex` at origin/main 696c4b602 (md5 0648e5f8…), tex 406–416, in the
proof of `cor:lef` and `cor:host`:

> Let `D_n(f)` be the diagonal matrix on `F_2^{Y_n}` with entry `f(y ∘ σ_n)` at `y`, let `P_ξ` be the
> permutation matrix of `ξ ∈ Λ`, and put `φ_n(∑_ξ f_ξ u_ξ) = ∑_ξ D_n(f_ξ) P_ξ`.  For fixed `f` and `ξ`
> and large `n`,
>   `P_ξ D_n(f) P_ξ⁻¹ = D_n(f ∘ ξ⁻¹)`,
> so for fixed `r, s ∈ R_Δ` and large `n`, `φ_n` is additive and multiplicative on `r, s`, and
> `φ_n(1) = I`.

* `modelDiag M n f = D_n(f)`, a ring homomorphism; `modelPerm M n ξ = P_ξ`
  (`modelPerm_apply`: the entry at `(i, j)` is `1` exactly when `i = ξ j`);
* `modelMap M n = φ_n`, additive (`SkewMonoidAlgebra.liftNC`), with the printed formula
  `modelMap_sum_coeff_mul_unit`;
* `eventually_modelPerm_mul_modelDiag` and `eventually_modelPerm_mul_modelDiag_mul_inv`: the displayed
  identity, for fixed `f, ξ` and large `n`.  The route is the printed one: `f ∘ ξ⁻¹` depends on finitely
  many coordinates, where the attached points move as `Λ` moves `Ω`;
* `eventually_modelMap_mul`: multiplicativity on fixed `r, s` for large `n`, through the monomials;
* `modelMap_one`: `φ_n(1) = I`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace Lamplighter

open Filter
open SkewMonoidAlgebra (single)

variable {Δ : Type*} [Group Δ] {T : Set Δ} (M : BallModelSequence Δ T) (n : ℕ)

/-- Evaluation at the attached points, `f ↦ (y ↦ f(y ∘ σ_n))`. -/
def attachEval : LocallyConstant (LampSpace Δ) (ZMod 2) →+* (ModelSpace M n → ZMod 2) where
  toFun f y := f (attach M n y)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **`D_n(f)`** (tex 407–408): the diagonal matrix with entry `f(y ∘ σ_n)` at `y`. -/
noncomputable def modelDiag :
    LocallyConstant (LampSpace Δ) (ZMod 2) →+* Matrix (ModelSpace M n) (ModelSpace M n) (ZMod 2) :=
  (Matrix.diagonalRingHom _ _).comp (attachEval M n)

theorem modelDiag_apply (f : LocallyConstant (LampSpace Δ) (ZMod 2)) :
    modelDiag M n f = Matrix.diagonal fun y => f (attach M n y) :=
  rfl

/-- **`P_ξ`** (tex 408–409): the permutation matrix of `ξ`. -/
noncomputable def modelPerm (ξ : LampAffine Δ) : Matrix (ModelSpace M n) (ModelSpace M n) (ZMod 2) :=
  Matrix.permMatrixHom (modelAct M n ξ)

theorem modelPerm_apply (ξ : LampAffine Δ) (i j : ModelSpace M n) :
    modelPerm M n ξ i j = if i = modelAct M n ξ j then 1 else 0 := by
  rw [modelPerm, Matrix.permMatrixHom_apply]
  show ((modelAct M n ξ)⁻¹.toPEquiv.toMatrix : Matrix _ _ (ZMod 2)) i j = _
  rw [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  by_cases h : i = modelAct M n ξ j
  · rw [if_pos (Option.mem_some_iff.2 (by rw [h]; simp)), if_pos h]
  · rw [if_neg (fun hm => h (by rw [← Option.mem_some_iff.1 hm]; simp)), if_neg h]

theorem modelPerm_one : modelPerm M n 1 = 1 := by
  rw [modelPerm, modelAct_one, map_one]

theorem eventually_modelPerm_mul (hT : Subgroup.closure T = ⊤) (ξ η : LampAffine Δ) :
    ∀ᶠ n in atTop, modelPerm M n (ξ * η) = modelPerm M n ξ * modelPerm M n η :=
  (eventually_modelAct_mul M hT ξ η).mono fun n hn => by
    rw [modelPerm, modelPerm, modelPerm, hn, map_mul]

/-- **`P_ξ D_n(f) = D_n(f ∘ ξ⁻¹) P_ξ`** for fixed `f, ξ` and large `n` (tex 410–414). -/
theorem eventually_modelPerm_mul_modelDiag (hT : Subgroup.closure T = ⊤) (ξ : LampAffine Δ)
    (f : LocallyConstant (LampSpace Δ) (ZMod 2)) :
    ∀ᶠ n in atTop, modelPerm M n ξ * modelDiag M n f =
      modelDiag M n
          (LocallyConstant.comap (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) ξ⁻¹) f) *
        modelPerm M n ξ := by
  obtain ⟨J, hJ⟩ := exists_finset_dependsOn Δ
    (LocallyConstant.comap (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) ξ⁻¹) f)
  refine (eventually_attach_modelAct M hT ξ J).mono fun n hn => ?_
  ext i j
  rw [modelDiag_apply, modelDiag_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, modelPerm_apply]
  by_cases hij : i = modelAct M n ξ j
  · rw [if_pos hij, one_mul, mul_one]
    show f (attach M n j) =
      LocallyConstant.comap (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) ξ⁻¹) f
        (attach M n i)
    rw [hij, hJ (attach M n (modelAct M n ξ j)) (ξ • attach M n j) fun h hh => hn j h hh,
      LocallyConstant.coe_comap_apply, ClopenGroupCoeff.smulMap_apply, inv_smul_smul]
  · rw [if_neg hij, zero_mul, mul_zero]

/-- **The displayed identity** `P_ξ D_n(f) P_ξ⁻¹ = D_n(f ∘ ξ⁻¹)` (tex 412–414). -/
theorem eventually_modelPerm_mul_modelDiag_mul_inv (hT : Subgroup.closure T = ⊤)
    (ξ : LampAffine Δ) (f : LocallyConstant (LampSpace Δ) (ZMod 2)) :
    ∀ᶠ n in atTop, modelPerm M n ξ * modelDiag M n f *
        Matrix.permMatrixHom (R := ZMod 2) (modelAct M n ξ)⁻¹ =
      modelDiag M n
        (LocallyConstant.comap (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) ξ⁻¹) f) :=
  (eventually_modelPerm_mul_modelDiag M hT ξ f).mono fun n hn => by
    rw [hn, mul_assoc, modelPerm, ← map_mul, mul_inv_cancel, map_one, mul_one]

/-! ## The maps `φ_n` -/

/-- **`φ_n(∑_ξ f_ξ u_ξ) = ∑_ξ D_n(f_ξ) P_ξ`** (tex 409–410). -/
noncomputable def modelMap : LampRing Δ →+ Matrix (ModelSpace M n) (ModelSpace M n) (ZMod 2) :=
  SkewMonoidAlgebra.liftNC
    ((modelDiag M n).toAddMonoidHom.comp
      (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm.toAddEquiv.toAddMonoidHom)
    (modelPerm M n)

theorem modelMap_single (ξ : LampAffine Δ)
    (a : ClopenGroupCoeff (LampAffine Δ) (LampSpace Δ) (ZMod 2)) :
    modelMap M n (single ξ a) =
      modelDiag M n ((ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm a) *
        modelPerm M n ξ :=
  SkewMonoidAlgebra.liftNC_single _ _ _ _

/-- The printed formula for `φ_n`. -/
theorem modelMap_sum_coeff_mul_unit (S : Finset (LampAffine Δ))
    (f : LampAffine Δ → LocallyConstant (LampSpace Δ) (ZMod 2)) :
    modelMap M n (∑ ξ ∈ S,
        ClopenGroupCrossedProduct.coeff (LampAffine Δ) (LampSpace Δ) (ZMod 2) (f ξ) *
          (ClopenGroupCrossedProduct.unit (LampAffine Δ) (LampSpace Δ) (ZMod 2) ξ : LampRing Δ)) =
      ∑ ξ ∈ S, modelDiag M n (f ξ) * modelPerm M n ξ := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [← ClopenGroupCrossedProduct.single_eq_coeff_mul_unit, modelMap_single,
    RingEquiv.symm_apply_apply]

/-- **`φ_n(1) = I`** (tex 416). -/
theorem modelMap_one : modelMap M n 1 = 1 := by
  rw [SkewMonoidAlgebra.one_def, modelMap_single, map_one, map_one, one_mul, modelPerm_one]

theorem of_symm_smul (ξ : LampAffine Δ)
    (a : ClopenGroupCoeff (LampAffine Δ) (LampSpace Δ) (ZMod 2)) :
    (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm (ξ • a) =
      LocallyConstant.comap (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) ξ⁻¹)
        ((ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm a) :=
  rfl

/-- Multiplicativity on monomials, for large `n`. -/
theorem eventually_modelMap_single_mul (hT : Subgroup.closure T = ⊤) (ξ η : LampAffine Δ)
    (a b : ClopenGroupCoeff (LampAffine Δ) (LampSpace Δ) (ZMod 2)) :
    ∀ᶠ n in atTop, modelMap M n (single ξ a * single η b) =
      modelMap M n (single ξ a) * modelMap M n (single η b) := by
  refine ((eventually_modelPerm_mul_modelDiag M hT ξ
    ((ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm b)).and
      (eventually_modelPerm_mul M hT ξ η)).mono fun n hn => ?_
  obtain ⟨h1, h2⟩ := hn
  have hL : modelMap M n (single ξ a * single η b) =
      modelDiag M n ((ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm a) *
        modelDiag M n
          (LocallyConstant.comap (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) ξ⁻¹)
            ((ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm b)) *
        modelPerm M n (ξ * η) := by
    rw [SkewMonoidAlgebra.single_mul_single, modelMap_single, ← map_mul]
    rfl
  rw [hL, h2, modelMap_single, modelMap_single]
  calc modelDiag M n ((ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm a) *
        modelDiag M n
          (LocallyConstant.comap (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) ξ⁻¹)
            ((ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm b)) *
        (modelPerm M n ξ * modelPerm M n η)
      = modelDiag M n ((ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm a) *
          (modelDiag M n
            (LocallyConstant.comap (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) ξ⁻¹)
              ((ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm b)) *
            modelPerm M n ξ) * modelPerm M n η := by
        simp only [mul_assoc]
    _ = modelDiag M n ((ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm a) *
          (modelPerm M n ξ *
            modelDiag M n ((ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm b)) *
          modelPerm M n η := by
        rw [h1]
    _ = modelDiag M n ((ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm a) *
          modelPerm M n ξ *
          (modelDiag M n ((ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2)).symm b) *
            modelPerm M n η) := by
        simp only [mul_assoc]

/-- An additive map that is multiplicative on the pairs of monomials of `r` and `s` is multiplicative
on `r, s`. -/
theorem modelMap_mul_of_single (r s : LampRing Δ)
    (h : ∀ ξ ∈ SkewMonoidAlgebra.support r, ∀ η ∈ SkewMonoidAlgebra.support s,
      modelMap M n (single ξ (SkewMonoidAlgebra.coeff r ξ) * single η (SkewMonoidAlgebra.coeff s η)) =
        modelMap M n (single ξ (SkewMonoidAlgebra.coeff r ξ)) *
          modelMap M n (single η (SkewMonoidAlgebra.coeff s η))) :
    modelMap M n (r * s) = modelMap M n r * modelMap M n s := by
  have hr : ∑ ξ ∈ SkewMonoidAlgebra.support r, single ξ (SkewMonoidAlgebra.coeff r ξ) = r :=
    (SkewMonoidAlgebra.sum_def' r single).symm.trans (SkewMonoidAlgebra.sum_single r)
  have hs : ∑ η ∈ SkewMonoidAlgebra.support s, single η (SkewMonoidAlgebra.coeff s η) = s :=
    (SkewMonoidAlgebra.sum_def' s single).symm.trans (SkewMonoidAlgebra.sum_single s)
  calc modelMap M n (r * s)
      = modelMap M n
          ((∑ ξ ∈ SkewMonoidAlgebra.support r, single ξ (SkewMonoidAlgebra.coeff r ξ)) *
            ∑ η ∈ SkewMonoidAlgebra.support s, single η (SkewMonoidAlgebra.coeff s η)) := by
        rw [hr, hs]
    _ = ∑ ξ ∈ SkewMonoidAlgebra.support r, ∑ η ∈ SkewMonoidAlgebra.support s,
          modelMap M n
            (single ξ (SkewMonoidAlgebra.coeff r ξ) * single η (SkewMonoidAlgebra.coeff s η)) := by
        rw [Finset.sum_mul, map_sum]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [Finset.mul_sum, map_sum]
    _ = ∑ ξ ∈ SkewMonoidAlgebra.support r, ∑ η ∈ SkewMonoidAlgebra.support s,
          modelMap M n (single ξ (SkewMonoidAlgebra.coeff r ξ)) *
            modelMap M n (single η (SkewMonoidAlgebra.coeff s η)) :=
        Finset.sum_congr rfl fun ξ hξ => Finset.sum_congr rfl fun η hη => h ξ hξ η hη
    _ = modelMap M n r * modelMap M n s := by
        conv_rhs => rw [← hr, ← hs]
        rw [map_sum, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        rw [Finset.mul_sum]

/-- **Multiplicativity** (tex 415–416): for fixed `r, s ∈ R_Δ` and large `n`. -/
theorem eventually_modelMap_mul (hT : Subgroup.closure T = ⊤) (r s : LampRing Δ) :
    ∀ᶠ n in atTop, modelMap M n (r * s) = modelMap M n r * modelMap M n s :=
  ((eventually_all_finset (SkewMonoidAlgebra.support r)).2 fun ξ _ =>
    (eventually_all_finset (SkewMonoidAlgebra.support s)).2 fun η _ =>
      eventually_modelMap_single_mul M hT ξ η _ _).mono fun n hn => modelMap_mul_of_single M n r s hn

end Lamplighter

open Lamplighter

/-- **The matrices and the maps `φ_n`** (tex 406–416): `D_n(f)` is diagonal with entry `f(y ∘ σ_n)`,
`P_ξ` is the permutation matrix of `ξ`, `φ_n(∑_ξ f_ξ u_ξ) = ∑_ξ D_n(f_ξ) P_ξ`; for fixed `f, ξ` and
large `n`, `P_ξ D_n(f) P_ξ⁻¹ = D_n(f ∘ ξ⁻¹)`; for fixed `r, s` and large `n`, `φ_n` is additive and
multiplicative on `r, s`; and `φ_n(1) = I`. -/
def PrintedLamplighterModelMatrices : Prop :=
  ∀ (Δ : Type) [Group Δ] (T : Set Δ), Subgroup.closure T = ⊤ → ∀ M : BallModelSequence Δ T,
    (∀ (n : ℕ) (f : LocallyConstant (LampSpace Δ) (ZMod 2)),
      modelDiag M n f = Matrix.diagonal fun y => f (attach M n y)) ∧
    (∀ (n : ℕ) (ξ : LampAffine Δ) (i j : ModelSpace M n),
      modelPerm M n ξ i j = if i = modelAct M n ξ j then 1 else 0) ∧
    (∀ (n : ℕ) (S : Finset (LampAffine Δ))
        (f : LampAffine Δ → LocallyConstant (LampSpace Δ) (ZMod 2)),
      modelMap M n (∑ ξ ∈ S,
          ClopenGroupCrossedProduct.coeff (LampAffine Δ) (LampSpace Δ) (ZMod 2) (f ξ) *
            (ClopenGroupCrossedProduct.unit (LampAffine Δ) (LampSpace Δ) (ZMod 2) ξ :
              LampRing Δ)) =
        ∑ ξ ∈ S, modelDiag M n (f ξ) * modelPerm M n ξ) ∧
    (∀ (f : LocallyConstant (LampSpace Δ) (ZMod 2)) (ξ : LampAffine Δ), ∀ᶠ n in Filter.atTop,
      modelPerm M n ξ * modelDiag M n f *
          Matrix.permMatrixHom (R := ZMod 2) (modelAct M n ξ)⁻¹ =
        modelDiag M n
          (LocallyConstant.comap (ClopenGroupCoeff.smulMap (LampAffine Δ) (LampSpace Δ) ξ⁻¹) f)) ∧
    (∀ r s : LampRing Δ, ∀ᶠ n in Filter.atTop,
      modelMap M n (r + s) = modelMap M n r + modelMap M n s ∧
        modelMap M n (r * s) = modelMap M n r * modelMap M n s) ∧
    (∀ n : ℕ, modelMap M n 1 = 1)

theorem printedLamplighterModelMatrices : PrintedLamplighterModelMatrices := fun _ _ _ hT M =>
  ⟨fun n f => modelDiag_apply M n f, fun n ξ i j => modelPerm_apply M n ξ i j,
    fun n S f => modelMap_sum_coeff_mul_unit M n S f,
    fun f ξ => eventually_modelPerm_mul_modelDiag_mul_inv M hT ξ f,
    fun r s => (eventually_modelMap_mul M hT r s).mono fun n hn => ⟨map_add _ r s, hn⟩,
    fun n => modelMap_one M n⟩

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedLamplighterModelMatrices

end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.eventually_modelMap_mul
#audit_axioms GroupApproximation.SimpleKazhdanSofic.Lamplighter.modelMap_one
