import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroTriOffPad
import GroupApproximation.BooneHigman.Metabelian.AbsorptionEndpoint
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidStep
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import GroupApproximation.Meta.AxiomGuard

/-!
# Lifting a doubly-fixed elementary matrix to the root subgroup avoiding `j` (lane bh-met-90l)

Let `h ∈ St_{k+2}(R)` have a matrix `D = padMat h` fixing both `e_{j.castSucc}` and `e_last`.
Then `D` is the identity padding of its `e₀`-block `B`, where
`e₀ = castSucc ∘ j.succAbove : Fin k ↪ Fin (k + 2)` (`czTriOff_padHom_of_fix`).  Also
`det B = det D = 1`.  So if `SL_k(R) = E_k(R)` (`Absorption.SpecialLinearInElementary`),
then `B` is elementary, `B = proj g'`, and `stab (indexMap j.succAbove g')` has matrix `D`
(`czTriOff_block_lift`).  Here `indexMap j.succAbove g'` lies in the root subgroup of
`St_{k+1}` avoiding `j` (`czTriOff_indexMap_mem_off`).

We also record that the word `T` of the collapse statement avoids every `j ∉ {i, k}`
(`czTriOff_T_mem`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

/-- `padMat` is the underlying matrix of the projection. -/
theorem czTriOff_padMat_eq {R : Type*} [Ring R] {N : ℕ} (g : St N R) :
    padMat g = (((projection g : elementaryGroup (Fin N) R) : (Matrix (Fin N) (Fin N) R)ˣ) :
      Matrix (Fin N) (Fin N) R) := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_padMat_eq

/-- Relabelling on `St` is identity padding on matrices. -/
theorem czTriOff_padMat_indexMap {R : Type*} [Ring R] {p N : ℕ} (e : Fin p ↪ Fin N)
    (g : St p R) : padMat (indexMap e g) = ElementaryPadding.padHom e (padMat g) := by
  rw [czTriOff_padMat_eq, projection_indexMap]
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_padMat_indexMap

/-- Equal matrices give equal projections. -/
theorem czTriOff_proj_eq_of_padMat {R : Type*} [Ring R] {N : ℕ} {g h : St N R}
    (hgh : padMat g = padMat h) : projection g = projection h := by
  rw [czTriOff_padMat_eq, czTriOff_padMat_eq] at hgh
  exact Subtype.ext (Units.ext hgh)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_proj_eq_of_padMat

/-- If `y` has the matrix of `q⁻¹ T`, then `q y` and `T` have the same projection. -/
theorem czTriOff_proj_mul_eq {R : Type*} [Ring R] {N : ℕ} {q T y : St N R}
    (h : padMat y = padMat (q⁻¹ * T)) : projection (q * y) = projection T := by
  apply czTriOff_proj_eq_of_padMat
  rw [map_mul padMat q y, h, ← map_mul padMat q (q⁻¹ * T), mul_inv_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_proj_mul_eq

/-- **Block lift.**  Given `SL_k(R) = E_k(R)`, a matrix of `St_{k+2}(R)` fixing
`e_{j.castSucc}` and `e_last` is the matrix of `stab (indexMap j.succAbove g')`. -/
theorem czTriOff_block_lift {R : Type*} [CommRing R] {k : ℕ}
    (hSL : Absorption.SpecialLinearInElementary R k) (j : Fin (k + 1))
    {h : St (k + 1 + 1) R} (hj : czTriOff_Fix j.castSucc (padMat h))
    (hL : czTriOff_Fix (Fin.last (k + 1)) (padMat h)) :
    ∃ g' : St k R, padMat (stab (k + 1) R (indexMap (Fin.succAboveEmb j) g')) = padMat h := by
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin k) (Fin k) R,
      B = (padMat h).submatrix (czTriOff_emb j) (czTriOff_emb j) := ⟨_, rfl⟩
  have hpad : ElementaryPadding.padHom (czTriOff_emb j) B = padMat h := by
    rw [hB]
    exact czTriOff_padHom_of_fix j hj hL
  have hdetD : (padMat h).det = 1 := by
    rw [czTriOff_padMat_eq]
    exact Absorption.suslin_det_eq_one_of_mem_elementaryGroup (projection h).2
  have hdetB : B.det = 1 := by
    rw [← czTriOff_det_padHom (czTriOff_emb j) B, hpad, hdetD]
  obtain ⟨Bu, hBu⟩ := (Matrix.isUnit_iff_isUnit_det B).mpr (by rw [hdetB]; exact isUnit_one)
  have hdetBu : Matrix.det (Bu : Matrix (Fin k) (Fin k) R) = 1 := by
    rw [hBu]
    exact hdetB
  have hmem : Bu ∈ elementaryGroup (Fin k) R := hSL Bu hdetBu
  obtain ⟨g', hg'⟩ := projection_surjective (I := Fin k) (R := R) ⟨Bu, hmem⟩
  refine ⟨g', ?_⟩
  rw [czTriOff_stab_indexMap, czTriOff_padMat_indexMap, czTriOff_padMat_eq g', hg']
  change ElementaryPadding.padHom (czTriOff_emb j) (Bu : Matrix (Fin k) (Fin k) R) = padMat h
  rw [hBu, hpad]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_block_lift

/-- The collapse word `T = Y X Y X` avoids every index `j ∉ {i, k}`. -/
theorem czTriOff_T_mem {R : Type*} [Ring R] {n : ℕ} {i kk j : Fin n} (hji : j ≠ i)
    (hjk : j ≠ kk) (α δ ζ η β γ : R) :
    padRow (Pi.single i α + Pi.single kk δ) * padCol (Pi.single i ζ + Pi.single kk η) *
        padRow (Pi.single i β) * padCol (Pi.single i γ) ∈ czStabGen_off R j.castSucc := by
  have h2 : ∀ a b : R, (Pi.single i a + Pi.single kk b : Fin n → R) j = 0 := by
    intro a b
    rw [Pi.add_apply, Pi.single_eq_of_ne hji, Pi.single_eq_of_ne hjk, add_zero]
  have h1 : ∀ a : R, (Pi.single i a : Fin n → R) j = 0 := fun a => Pi.single_eq_of_ne hji a
  exact mul_mem (mul_mem (mul_mem (czStabGen_padRow_mem_off (h2 α δ))
    (czStabGen_padCol_mem_off (h2 ζ η))) (czStabGen_padRow_mem_off (h1 β)))
    (czStabGen_padCol_mem_off (h1 γ))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_T_mem

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
