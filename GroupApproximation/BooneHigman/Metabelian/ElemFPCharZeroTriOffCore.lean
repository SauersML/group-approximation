import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroTriOffIdent
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroTriOffLift
import GroupApproximation.Meta.AxiomGuard

/-!
# The `K₂`-free collapse over a ring with `SL_k = E_k` (lane bh-met-90l)

Here `R` is a commutative ring with `SL_k(R) = E_k(R)`.  Let `T ∈ St_{k+2}(R)` lie in the
root subgroups avoiding `j.castSucc` and avoiding `j'.castSucc`, for some `j ≠ j'` in
`Fin (k + 1)`.  We produce `g₂` in the root subgroup of `St_{k+1}` avoiding `j`, and
vectors `v, w, c, w'` vanishing at `j`, such that
`proj (X_v Y_w X_c Y_{w'} · stab g₂) = proj T` (`czTriOff_core`).

Proof.  Let `(μ, s)` be the last column of `M = padMat T` and `(ρ, r)` the last row of
`M⁻¹`.  Then `ρ ⬝ μ + r s = 1`, and `μ, ρ` vanish at `j` and at `j'`, since `T` avoids both.
The word `q = X_v Y_w X_c Y_{w'}` of `czTriOff_word_mulVec` (pivot `j'`) has vectors
vanishing at `j`, so `q` avoids `j.castSucc`.  It matches the last column of `M` and the
last row of `M⁻¹`, so `q⁻¹ T` fixes `e_last` and `e_{j.castSucc}`.  By `czTriOff_block_lift`,
`q⁻¹ T` has the matrix of `stab g₂` with `g₂ = indexMap j.succAbove g'`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

/-- **Core.**  The `K₂`-free collapse for a word avoiding two distinct indices. -/
theorem czTriOff_core {R : Type*} [CommRing R] {k : ℕ}
    (hSL : Absorption.SpecialLinearInElementary R k) {j j' : Fin (k + 1)} (hjj' : j ≠ j')
    {T : St (k + 1 + 1) R} (hTj : T ∈ czStabGen_off R j.castSucc)
    (hTj' : T ∈ czStabGen_off R j'.castSucc) :
    ∃ (g₂ : St (k + 1) R) (v w c w' : Fin (k + 1) → R), g₂ ∈ czStabGen_off R j ∧
      v j = 0 ∧ w j = 0 ∧ c j = 0 ∧ w' j = 0 ∧
      projection (stab (k + 1) R 1 * padCol v * padRow w * padCol c * padRow w' *
        stab (k + 1) R g₂) = projection T := by
  obtain ⟨μu, s, hμ⟩ : ∃ (μu : Fin (k + 1) → R) (s : R),
      padMat T *ᵥ surjStabVec (0 : Fin (k + 1) → R) 1 = surjStabVec μu s :=
    ⟨_, _, (czTriOff_eta _).symm⟩
  obtain ⟨ρu, r, hρ⟩ : ∃ (ρu : Fin (k + 1) → R) (r : R),
      surjStabVec (0 : Fin (k + 1) → R) 1 ᵥ* padMat T⁻¹ = surjStabVec ρu r :=
    ⟨_, _, (czTriOff_eta _).symm⟩
  have hdot : ρu ⬝ᵥ μu + r * s = 1 := by
    have h1 : (surjStabVec (0 : Fin (k + 1) → R) 1 ᵥ* padMat T⁻¹) ⬝ᵥ
        (padMat T *ᵥ surjStabVec (0 : Fin (k + 1) → R) 1) =
        surjStabVec (0 : Fin (k + 1) → R) 1 ⬝ᵥ surjStabVec (0 : Fin (k + 1) → R) 1 := by
      rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul padMat T⁻¹ T,
        inv_mul_cancel, map_one, Matrix.one_mulVec]
    rw [hρ, hμ, czTriOff_dot_split, czTriOff_dot_split, dotProduct_zero, zero_add,
      mul_one] at h1
    exact h1
  have hcj : j.castSucc ≠ Fin.last (k + 1) := (Fin.castSucc_lt_last j).ne
  have hcj' : j'.castSucc ≠ Fin.last (k + 1) := (Fin.castSucc_lt_last j').ne
  have hμj : μu j = 0 := by
    have h := czTriOff_mulVec_eq_zero hTj hcj
    rwa [hμ, surjStabVec_castSucc] at h
  have hμj' : μu j' = 0 := by
    have h := czTriOff_mulVec_eq_zero hTj' hcj'
    rwa [hμ, surjStabVec_castSucc] at h
  have hρj : ρu j = 0 := by
    have h := czTriOff_vecMul_eq_zero (inv_mem hTj) hcj
    rwa [hρ, surjStabVec_castSucc] at h
  have hρj' : ρu j' = 0 := by
    have h := czTriOff_vecMul_eq_zero (inv_mem hTj') hcj'
    rwa [hρ, surjStabVec_castSucc] at h
  have hv : (Pi.single j' (-1) : Fin (k + 1) → R) j = 0 := Pi.single_eq_of_ne hjj' _
  have hw : (-(ρu + Pi.single j' (r - 1)) : Fin (k + 1) → R) j = 0 := by
    rw [Pi.neg_apply, Pi.add_apply, hρj, Pi.single_eq_of_ne hjj', add_zero, neg_zero]
  have hc : (μu + Pi.single j' s : Fin (k + 1) → R) j = 0 := by
    rw [Pi.add_apply, hμj, Pi.single_eq_of_ne hjj', add_zero]
  have hw' : (-(ρu + r • -(ρu + Pi.single j' (r - 1))) : Fin (k + 1) → R) j = 0 := by
    rw [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, hw, smul_zero, hρj, add_zero, neg_zero]
  have hq₀ : padCol (Pi.single j' (-1) : Fin (k + 1) → R) *
      padRow (-(ρu + Pi.single j' (r - 1))) * padCol (μu + Pi.single j' s) *
      padRow (-(ρu + r • -(ρu + Pi.single j' (r - 1)))) ∈ czStabGen_off R j.castSucc :=
    mul_mem (mul_mem (mul_mem (czStabGen_padCol_mem_off hv) (czStabGen_padRow_mem_off hw))
      (czStabGen_padCol_mem_off hc)) (czStabGen_padRow_mem_off hw')
  have ha := czTriOff_word_mulVec j' μu ρu s r hμj' hρj' hdot
  have hb := czTriOff_word_vecMul j' μu ρu s r hμj' hρj' hdot
  have hfixL := czTriOff_fix_last_of_word hμ hρ ha hb
  have hfixj := czTriOff_fix_of_mem (mul_mem (inv_mem hq₀) hTj)
  obtain ⟨g', hg'⟩ := czTriOff_block_lift hSL j hfixj hfixL
  refine ⟨indexMap (Fin.succAboveEmb j) g', Pi.single j' (-1), -(ρu + Pi.single j' (r - 1)),
    μu + Pi.single j' s, -(ρu + r • -(ρu + Pi.single j' (r - 1))),
    czTriOff_indexMap_mem_off j g', hv, hw, hc, hw', ?_⟩
  rw [map_one (stab (k + 1) R), one_mul]
  exact czTriOff_proj_mul_eq hg'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czTriOff_core

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
