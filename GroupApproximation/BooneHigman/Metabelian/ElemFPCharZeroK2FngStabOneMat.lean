import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroTriOffLift
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroTriOffVec
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabLengthSet
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabRow
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabFactorPar
import GroupApproximation.BooneHigman.Metabelian.VdKStabPID
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidInstances
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngTorusOne
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# Matrix-level length reduction in `St_3(ℤ[1/1])` (lane bh-met-92z, 2)

Every `y ∈ St_3(ℤ[1/1])` has the *matrix* of an element of `H X Y X Y H`
(`czK2FngStabOne_mat`).  Here `H = stab St_2`, `X = padCol`, `Y = padRow`.

The argument is Gaussian elimination.
1. The last row `(r, t)` of `padMat y` is unimodular, with witness `padMat y⁻¹ e_L`.
2. `sr(ℤ[1/1]) ≤ 2` (`vdkStab_stableRangeLE_two_of_pid`) gives `b` with `r + t b` unimodular.
   Say `(r + t b) ⬝ u = 1`.
3. Right-multiplying by `Y(b) X((1 - t) u) Y(-(r + t b))` turns the last row into `e_L`.
4. Then left-multiplying by `X(-μ)` also turns the last column into `e_L`.
5. The result is the padding of an `SL_2(ℤ[1/1])` matrix.  That matrix is elementary
   (`specialLinearInElementary_away`), so it is the matrix of some `stab g'`
   (`czK2FngStabOne_lift_of_fixLast`).

The only inputs are repository theorems.  No hypothesis is added.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

local notation "R₁" => Localization.Away ((1 : ℕ) : ℤ)

/-- Given `SL_k(R) = E_k(R)`, a matrix of `St_{k+1}(R)` fixing `e_last` is the matrix of a
stabilised element. -/
theorem czK2FngStabOne_lift_of_fixLast {R : Type*} [CommRing R] {k : ℕ}
    (hSL : Absorption.SpecialLinearInElementary R k) {h : St (k + 1) R}
    (hL : czTriOff_Fix (Fin.last k) (padMat h)) :
    ∃ g' : St k R, padMat (stab k R g') = padMat h := by
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin k) (Fin k) R,
      B = (padMat h).submatrix Fin.castSuccEmb Fin.castSuccEmb := ⟨_, rfl⟩
  have hpad : ElementaryPadding.padHom Fin.castSuccEmb B = padMat h := by
    rw [hB]
    apply czTriOff_padHom_submatrix
    intro a b hab
    rcases hab with ha | hb
    · rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl
      · exact (ha ⟨a', rfl⟩).elim
      · exact czTriOff_fix_row hL b
    · rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · exact (hb ⟨b', rfl⟩).elim
      · exact czTriOff_fix_col hL a
  have hdetD : (padMat h).det = 1 := by
    rw [czTriOff_padMat_eq]
    exact Absorption.suslin_det_eq_one_of_mem_elementaryGroup (projection h).2
  have hdetB : B.det = 1 := by
    rw [← czTriOff_det_padHom Fin.castSuccEmb B, hpad, hdetD]
  obtain ⟨Bu, hBu⟩ := (Matrix.isUnit_iff_isUnit_det B).mpr (by rw [hdetB]; exact isUnit_one)
  have hdetBu : Matrix.det (Bu : Matrix (Fin k) (Fin k) R) = 1 := by
    rw [hBu]
    exact hdetB
  have hmem : Bu ∈ elementaryGroup (Fin k) R := hSL Bu hdetBu
  obtain ⟨g', hg'⟩ := projection_surjective (I := Fin k) (R := R) ⟨Bu, hmem⟩
  refine ⟨g', ?_⟩
  show padMat (indexMap Fin.castSuccEmb g') = padMat h
  rw [czTriOff_padMat_indexMap, czTriOff_padMat_eq g', hg']
  change ElementaryPadding.padHom Fin.castSuccEmb (Bu : Matrix (Fin k) (Fin k) R) = padMat h
  rw [hBu, hpad]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_lift_of_fixLast

/-- `padCol (-v) = (padCol v)⁻¹`. -/
theorem czK2FngStabOne_padCol_neg {R : Type*} [Ring R] {n : ℕ} (v : Fin n → R) :
    padCol (-v) = (padCol v)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← padCol_add, neg_add_cancel, padCol_zero])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_padCol_neg

/-- `padRow (-v) = (padRow v)⁻¹`. -/
theorem czK2FngStabOne_padRow_neg {R : Type*} [Ring R] {n : ℕ} (v : Fin n → R) :
    padRow (-v) = (padRow v)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← padRow_add, neg_add_cancel, padRow_zero])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_padRow_neg

/-- `ℤ[1/1]` is a principal ideal domain. -/
theorem czK2FngStabOne_isPID : IsDomain R₁ ∧ IsPrincipalIdealRing R₁ :=
  ⟨IsLocalization.isDomain_localization
      (powers_le_nonZeroDivisors_of_noZeroDivisors (Nat.cast_ne_zero.2 one_ne_zero)),
    IsPrincipalIdealRing.of_surjective (R := ℤ) czK2FngTorus_oneRingEquiv
      czK2FngTorus_oneRingEquiv.surjective⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_isPID

/-- **Matrix length reduction.**  Every element of `St_3(ℤ[1/1])` has the matrix of an element
of `H X Y X Y H`. -/
theorem czK2FngStabOne_mat (y : St (2 + 1) R₁) :
    ∃ y' : St (2 + 1) R₁, SurjStabLengthMem y' ∧ padMat y' = padMat y := by
  haveI : IsDomain R₁ := czK2FngStabOne_isPID.1
  haveI : IsPrincipalIdealRing R₁ := czK2FngStabOne_isPID.2
  obtain ⟨r, t, hρ⟩ : ∃ (r : Fin 2 → R₁) (t : R₁),
      surjStabVec (0 : Fin 2 → R₁) 1 ᵥ* padMat y = surjStabVec r t :=
    ⟨_, _, (czTriOff_eta _).symm⟩
  have hU : ElemFP.vdkStab_IsUnimodular (surjStabVec r t) := by
    refine ⟨padMat y⁻¹ *ᵥ surjStabVec (0 : Fin 2 → R₁) 1, ?_⟩
    change surjStabVec r t ⬝ᵥ (padMat y⁻¹ *ᵥ surjStabVec (0 : Fin 2 → R₁) 1) = 1
    rw [← hρ, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul padMat y y⁻¹,
      mul_inv_cancel, map_one, Matrix.one_mulVec, czTriOff_dot_split, zero_dotProduct,
      zero_add, mul_one]
  obtain ⟨b, u, hu⟩ := ElemFP.vdkStab_stableRangeLE_two_of_pid R₁ 2 le_rfl _ hU
  have hred : ∀ i, ElemFP.vdkStab_reduceRow (surjStabVec r t) b i = (r + t • b) i := by
    intro i
    show surjStabVec r t (Fin.castSucc i) + b i * surjStabVec r t (Fin.last 2) = r i + t * b i
    rw [surjStabVec_castSucc, surjStabVec_last, mul_comm (b i) t]
  have hw : (r + t • b) ⬝ᵥ u = 1 := by
    rw [← hu, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by rw [hred i]
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : St (2 + 1) R₁,
      y₁ = y * padRow b * padCol ((1 - t) • u) * padRow (-(r + t • b)) := ⟨_, rfl⟩
  have hrow : surjStabVec (0 : Fin 2 → R₁) 1 ᵥ* padMat y₁ = surjStabVec 0 1 := by
    rw [hy₁, map_mul, map_mul, map_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      ← Matrix.vecMul_vecMul, hρ, czTriOff_vecMul_padRow, surjStabFactor_vecMul_padCol,
      dotProduct_smul, hw, smul_eq_mul, mul_one, add_sub_cancel, surjStab_vecMul_padRow,
      add_neg_cancel]
  obtain ⟨μ, s, hcol⟩ : ∃ (μ : Fin 2 → R₁) (s : R₁),
      padMat y₁ *ᵥ surjStabVec (0 : Fin 2 → R₁) 1 = surjStabVec μ s :=
    ⟨_, _, (czTriOff_eta _).symm⟩
  have hs : s = 1 := by
    have h := congrArg (fun v => surjStabVec (0 : Fin 2 → R₁) 1 ⬝ᵥ v) hcol
    simp only [Matrix.dotProduct_mulVec, hrow, czTriOff_dot_split, zero_dotProduct, zero_add,
      one_mul] at h
    exact h.symm
  subst hs
  obtain ⟨y₂, hy₂⟩ : ∃ y₂ : St (2 + 1) R₁, y₂ = padCol (-μ) * y₁ := ⟨_, rfl⟩
  have hfix : czTriOff_Fix (Fin.last 2) (padMat y₂) := by
    refine ⟨?_, ?_⟩
    · rw [← czTriOff_e_eq, hy₂, map_mul, ← Matrix.mulVec_mulVec, hcol, czTriOff_padCol_mulVec,
        one_smul, add_neg_cancel]
    · rw [← czTriOff_e_eq, hy₂, map_mul, ← Matrix.vecMul_vecMul, surjStabFactor_vecMul_padCol,
        zero_dotProduct, add_zero, hrow]
  obtain ⟨g', hg'⟩ := czK2FngStabOne_lift_of_fixLast
    (Absorption.specialLinearInElementary_away 1 (N := 2) (by omega)) hfix
  have hmem : SurjStabLengthMem (stab 2 R₁ g' * padCol 0 * padRow (r + t • b) *
      padCol (-((1 - t) • u)) * padRow (-b) * stab 2 R₁ 1) :=
    ⟨g', 1, 0, r + t • b, -((1 - t) • u), -b, rfl⟩
  refine ⟨_, surjStabLength_mem_padCol_mul hmem μ, ?_⟩
  have hy : padCol μ * y₂ * padRow (r + t • b) * padCol (-((1 - t) • u)) * padRow (-b) = y := by
    simp only [hy₂, hy₁, czK2FngStabOne_padCol_neg, czK2FngStabOne_padRow_neg]
    group
  rw [← hy]
  simp only [map_mul, map_one, padCol_zero, mul_one, hg', mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngStabOne_mat

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
