import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroTriOffVec
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# The `X Y X Y` word matching the last row and column (lane bh-met-90l)

Here `R` is a commutative ring.  Let `M` be an elementary matrix in `E_{n+1}(R)`, with last
column `(μ, s)` and with `(ρ, r)` the last row of `M⁻¹`.  Then `ρ ⬝ μ + r s = 1`.  Fix an
index `j'` with `μ j' = ρ j' = 0` and put

* `v = -e_{j'}`,  `w = -(ρ + (r - 1) e_{j'})`,  `c = μ + s e_{j'}`,  `w' = -(ρ + r w)`,
* `G = X_v Y_w X_c Y_{w'}`, where `X = padCol` and `Y = padRow`.

Then `G e_L = (μ, s)` (`czTriOff_word_mulVec`) and `(ρ, r) G = e_L` (`czTriOff_word_vecMul`).
The row computation uses `(ρ + r w) ⬝ c = 1 - r`, and the column computation uses
`1 + w ⬝ c = s`.  Both follow from `ρ ⬝ μ + r s = 1` together with `μ j' = ρ j' = 0`.
So `G⁻¹ M` fixes `e_L` on both sides (`czTriOff_fix_last_of_word`).

Truth check on paper, with `n = 1` and `j'` the only index, so `μ = ρ = 0` and `r s = 1`:
`c = s`, `w = 1 - r`, `1 + w c = 1 + s - r s = s`.  Also `ρ + r w = r - r²` and
`(r - r²) s = 1 - r`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Column side: `G e_L = (μ, s)`. -/
theorem czTriOff_word_mulVec (j' : Fin n) (μu ρu : Fin n → R) (s r : R) (hμ : μu j' = 0)
    (hρ : ρu j' = 0) (hdot : ρu ⬝ᵥ μu + r * s = 1) :
    padMat (padCol (Pi.single j' (-1)) * padRow (-(ρu + Pi.single j' (r - 1))) *
        padCol (μu + Pi.single j' s) * padRow (-(ρu + r • -(ρu + Pi.single j' (r - 1))))) *ᵥ
      surjStabVec (0 : Fin n → R) 1 = surjStabVec μu s := by
  have hs : 1 + -(ρu + Pi.single j' (r - 1)) ⬝ᵥ (μu + Pi.single j' s) = s := by
    rw [neg_dotProduct, add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_single,
      dotProduct_single, single_dotProduct, Pi.single_eq_same, hρ, hμ]
    linear_combination (-1 : R) * hdot
  rw [map_mul, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, czTriOff_padRow_mulVec, dotProduct_zero, add_zero,
    surjStab_padCol_mulVec_one, zero_add, czTriOff_padRow_mulVec, hs, czTriOff_padCol_mulVec,
    czTriOff_smul_single, add_assoc, ← Pi.single_add, mul_neg_one, add_neg_cancel,
    Pi.single_zero, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_word_mulVec

/-- Row side: `(ρ, r) G = e_L`. -/
theorem czTriOff_word_vecMul (j' : Fin n) (μu ρu : Fin n → R) (s r : R) (hμ : μu j' = 0)
    (hρ : ρu j' = 0) (hdot : ρu ⬝ᵥ μu + r * s = 1) :
    surjStabVec ρu r ᵥ*
        padMat (padCol (Pi.single j' (-1)) * padRow (-(ρu + Pi.single j' (r - 1))) *
          padCol (μu + Pi.single j' s) * padRow (-(ρu + r • -(ρu + Pi.single j' (r - 1))))) =
      surjStabVec (0 : Fin n → R) 1 := by
  have ht : r + (ρu + r • -(ρu + Pi.single j' (r - 1))) ⬝ᵥ (μu + Pi.single j' s) = 1 := by
    rw [add_dotProduct, smul_dotProduct, neg_dotProduct, add_dotProduct, dotProduct_add,
      dotProduct_add, dotProduct_single, dotProduct_single, single_dotProduct,
      Pi.single_eq_same, hρ, hμ, smul_eq_mul]
    linear_combination (1 - r) * hdot
  rw [map_mul, map_mul, map_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
    ← Matrix.vecMul_vecMul, surjStabFactor_vecMul_padCol, dotProduct_single, hρ, zero_mul,
    add_zero, czTriOff_vecMul_padRow, surjStabFactor_vecMul_padCol, ht, surjStab_vecMul_padRow,
    add_neg_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_word_vecMul

/-- If `q` matches the last column of `T` and the last row of `T⁻¹`, then `q⁻¹ T` fixes
`e_L` on both sides. -/
theorem czTriOff_fix_last_of_word {T q : St (n + 1) R} {μu ρu : Fin n → R} {s r : R}
    (hμ : padMat T *ᵥ surjStabVec (0 : Fin n → R) 1 = surjStabVec μu s)
    (hρ : surjStabVec (0 : Fin n → R) 1 ᵥ* padMat T⁻¹ = surjStabVec ρu r)
    (ha : padMat q *ᵥ surjStabVec (0 : Fin n → R) 1 = surjStabVec μu s)
    (hb : surjStabVec ρu r ᵥ* padMat q = surjStabVec (0 : Fin n → R) 1) :
    czTriOff_Fix (Fin.last n) (padMat (q⁻¹ * T)) := by
  have he := czTriOff_e_eq (R := R) (n := n)
  have h1 : surjStabVec (0 : Fin n → R) 1 ᵥ* padMat q⁻¹ = surjStabVec ρu r := by
    rw [← hb, Matrix.vecMul_vecMul, ← map_mul padMat q q⁻¹, mul_inv_cancel, map_one,
      Matrix.vecMul_one]
  refine ⟨?_, ?_⟩
  · rw [← he, map_mul padMat q⁻¹ T, ← Matrix.mulVec_mulVec, hμ, ← ha, Matrix.mulVec_mulVec,
      ← map_mul padMat q⁻¹ q, inv_mul_cancel, map_one, Matrix.one_mulVec]
  · rw [← he, map_mul padMat q⁻¹ T, ← Matrix.vecMul_vecMul, h1, ← hρ, Matrix.vecMul_vecMul,
      ← map_mul padMat T⁻¹ T, inv_mul_cancel, map_one, Matrix.vecMul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_fix_last_of_word

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
