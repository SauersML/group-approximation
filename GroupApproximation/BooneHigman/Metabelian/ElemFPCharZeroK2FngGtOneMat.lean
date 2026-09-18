import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngStabOneMat
import GroupApproximation.BooneHigman.Metabelian.SuslinKillLift
import GroupApproximation.Meta.AxiomGuard

/-!
# Matrix-level length reduction in `St_3(R)` for a PID `R` (lane bh-met-93o, 1)

This file generalises `czK2FngStabOne_mat` from `ℤ[1/1]` to any principal ideal domain `R`
with `SL_2(R) = E_2(R)`.  Every `y ∈ St_3(R)` then has the *matrix* of an element of
`H X Y X Y H` (`czK2FngGtOne_mat`).  Here `H = stab St_2`, `X = padCol`, `Y = padRow`.

The proof is the same Gaussian elimination.  It uses `sr(R) ≤ 2`
(`vdkStab_stableRangeLE_two_of_pid`) and `SL_2(R) = E_2(R)`.

For `R = ℤ[1/m]` with `m > 0`:
* `IsDomain` comes from `IsLocalization.isDomain_localization`;
* `IsPrincipalIdealRing` comes from `Absorption.suslinKill_away_pid`;
* `SL_2 = E_2` comes from `Absorption.specialLinearInElementary_away`.

This gives `czK2FngGtOne_mat_away`.  No hypothesis is added.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

/-- `ℤ[1/m]` is a domain for `m > 0`. -/
theorem czK2FngGtOne_isDomain {m : ℕ} (hm : 0 < m) : IsDomain (Localization.Away (m : ℤ)) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Nat.cast_ne_zero.2 (by omega)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOne_isDomain

/-- **Matrix length reduction over a PID.**  Every element of `St_3(R)` has the matrix of an
element of `H X Y X Y H`. -/
theorem czK2FngGtOne_mat {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (hSL : Absorption.SpecialLinearInElementary R 2) (y : St (2 + 1) R) :
    ∃ y' : St (2 + 1) R, SurjStabLengthMem y' ∧ padMat y' = padMat y := by
  obtain ⟨r, t, hρ⟩ : ∃ (r : Fin 2 → R) (t : R),
      surjStabVec (0 : Fin 2 → R) 1 ᵥ* padMat y = surjStabVec r t :=
    ⟨_, _, (czTriOff_eta _).symm⟩
  have hU : ElemFP.vdkStab_IsUnimodular (surjStabVec r t) := by
    refine ⟨padMat y⁻¹ *ᵥ surjStabVec (0 : Fin 2 → R) 1, ?_⟩
    change surjStabVec r t ⬝ᵥ (padMat y⁻¹ *ᵥ surjStabVec (0 : Fin 2 → R) 1) = 1
    rw [← hρ, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul padMat y y⁻¹,
      mul_inv_cancel, map_one, Matrix.one_mulVec, czTriOff_dot_split, zero_dotProduct,
      zero_add, mul_one]
  obtain ⟨b, u, hu⟩ := ElemFP.vdkStab_stableRangeLE_two_of_pid R 2 le_rfl _ hU
  have hred : ∀ i, ElemFP.vdkStab_reduceRow (surjStabVec r t) b i = (r + t • b) i := by
    intro i
    rw [ElemFP.vdkStab_reduceRow_apply, surjStabVec_castSucc, surjStabVec_last,
      mul_comm (b i) t]
    rfl
  have hw : (r + t • b) ⬝ᵥ u = 1 := by
    rw [← hu, dotProduct]
    exact Finset.sum_congr rfl fun i _ => by rw [hred i]
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : St (2 + 1) R,
      y₁ = y * padRow b * padCol ((1 - t) • u) * padRow (-(r + t • b)) := ⟨_, rfl⟩
  have hrow : surjStabVec (0 : Fin 2 → R) 1 ᵥ* padMat y₁ = surjStabVec 0 1 := by
    rw [hy₁, map_mul, map_mul, map_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      ← Matrix.vecMul_vecMul, hρ, czTriOff_vecMul_padRow, surjStabFactor_vecMul_padCol,
      dotProduct_smul, hw, smul_eq_mul, mul_one, add_sub_cancel, surjStab_vecMul_padRow,
      add_neg_cancel]
  obtain ⟨μ, s, hcol⟩ : ∃ (μ : Fin 2 → R) (s : R),
      padMat y₁ *ᵥ surjStabVec (0 : Fin 2 → R) 1 = surjStabVec μ s :=
    ⟨_, _, (czTriOff_eta _).symm⟩
  have hs : s = 1 := by
    have h := congrArg (fun v => surjStabVec (0 : Fin 2 → R) 1 ⬝ᵥ v) hcol
    simp only [Matrix.dotProduct_mulVec, hrow, czTriOff_dot_split, zero_dotProduct, zero_add,
      one_mul] at h
    exact h.symm
  subst hs
  obtain ⟨y₂, hy₂⟩ : ∃ y₂ : St (2 + 1) R, y₂ = padCol (-μ) * y₁ := ⟨_, rfl⟩
  have hfix : czTriOff_Fix (Fin.last 2) (padMat y₂) := by
    refine ⟨?_, ?_⟩
    · rw [← czTriOff_e_eq, hy₂, map_mul, ← Matrix.mulVec_mulVec, hcol, czTriOff_padCol_mulVec,
        one_smul, add_neg_cancel]
    · rw [← czTriOff_e_eq, hy₂, map_mul, ← Matrix.vecMul_vecMul, surjStabFactor_vecMul_padCol,
        zero_dotProduct, add_zero, hrow]
  obtain ⟨g', hg'⟩ := czK2FngStabOne_lift_of_fixLast hSL hfix
  have hmem : SurjStabLengthMem (stab 2 R g' * padCol 0 * padRow (r + t • b) *
      padCol (-((1 - t) • u)) * padRow (-b) * stab 2 R 1) :=
    ⟨g', 1, 0, r + t • b, -((1 - t) • u), -b, rfl⟩
  refine ⟨_, surjStabLength_mem_padCol_mul hmem μ, ?_⟩
  have hy : padCol μ * y₂ * padRow (r + t • b) * padCol (-((1 - t) • u)) * padRow (-b) = y := by
    simp only [hy₂, hy₁, czK2FngStabOne_padCol_neg, czK2FngStabOne_padRow_neg]
    group
  rw [← hy]
  simp only [map_mul, map_one, padCol_zero, mul_one, hg', mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOne_mat

/-- **Matrix length reduction over `ℤ[1/m]`, `m > 0`.** -/
theorem czK2FngGtOne_mat_away {m : ℕ} (hm : 0 < m)
    (y : St (2 + 1) (Localization.Away (m : ℤ))) :
    ∃ y' : St (2 + 1) (Localization.Away (m : ℤ)), SurjStabLengthMem y' ∧
      padMat y' = padMat y := by
  haveI : IsDomain (Localization.Away (m : ℤ)) := czK2FngGtOne_isDomain hm
  haveI : IsPrincipalIdealRing (Localization.Away (m : ℤ)) := Absorption.suslinKill_away_pid m
  exact czK2FngGtOne_mat (Absorption.specialLinearInElementary_away m (N := 2) (by omega)) y

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOne_mat_away

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
