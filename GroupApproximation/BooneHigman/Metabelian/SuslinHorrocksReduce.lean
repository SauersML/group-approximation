import GroupApproximation.BooneHigman.Metabelian.SuslinMonicEuclid
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Local Horrocks, part 1: column operations on one row

Lane `bh-met-90a`.  Matrix bookkeeping for the local Horrocks theorem
(`SuslinHorrocksRow.lean`): a row of an invertible matrix over `R[X]`, `R` local, with a monic
entry is carried to a standard basis row by right multiplication by elementary matrices (column
operations).  This file provides:

* `suslinHorrocks_exists_row_modByMonic`: Euclidean reduction of row `r` modulo its monic entry
  at `t` (the row version of `suslinMonic_exists_row_modByMonic`);
* `suslinHorrocks_clear_of_eq_one`: a row with a `1` at `t` is cleared to `e_t`;
* `suslinHorrocks_move_single`: a row `e_s` is moved to `e_r`;
* `suslinHorrocks_two_col_apply`: two column additions into the same column;
* `suslinHorrocks_exists_residue_ne_zero`: over a local ring, if the monic entry at `t` has
  positive degree, some other entry of the row is nonzero modulo the maximal ideal (because the
  row is unimodular).

No locality is used except in the last lemma.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

open RankNElimination

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- **Euclidean reduction of row `r` modulo its entry at `t`.** -/
theorem suslinHorrocks_exists_row_modByMonic (A : (Matrix ι ι (Polynomial R))ˣ) (r t : ι) :
    ∃ F ∈ elementaryGroup ι (Polynomial R),
      ∀ c : ι, ((A * F : (Matrix ι ι (Polynomial R))ˣ) : Matrix ι ι (Polynomial R)) r c =
        if c = t then (A : Matrix ι ι (Polynomial R)) r t
        else (A : Matrix ι ι (Polynomial R)) r c %ₘ (A : Matrix ι ι (Polynomial R)) r t := by
  refine ⟨(rightClearFactors t (fun k ↦ -((A : Matrix ι ι (Polynomial R)) r k /ₘ
      (A : Matrix ι ι (Polynomial R)) r t)) (otherIndices t)).prod,
    rightClearFactors_prod_mem t _, fun c ↦ ?_⟩
  rw [Units.val_mul, mul_rightClearFactors_apply (A : Matrix ι ι (Polynomial R)) t _
    (otherIndices t) (otherIndices_nodup t)]
  by_cases hc : c = t
  · rw [hc, if_neg (fun h ↦ (mem_otherIndices_values_iff t t).1 h rfl), if_pos rfl]
  · rw [if_pos ((mem_otherIndices_values_iff t c).2 hc), if_neg hc]
    simp only [Polynomial.modByMonic_eq_sub_mul_div, mul_neg, sub_eq_add_neg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinHorrocks_exists_row_modByMonic

/-- **Clearing a row with a unit entry `1`.**  If row `r` has entry `1` at `t`, an elementary
right factor turns row `r` into `e_t`. -/
theorem suslinHorrocks_clear_of_eq_one {R' : Type*} [Ring R'] (M : (Matrix ι ι R')ˣ) (r t : ι)
    (h1 : (M : Matrix ι ι R') r t = 1) :
    ∃ F ∈ elementaryGroup ι R',
      ∀ c : ι, ((M * F : (Matrix ι ι R')ˣ) : Matrix ι ι R') r c = if c = t then 1 else 0 := by
  refine ⟨(rightClearFactors t (fun k ↦ -(M : Matrix ι ι R') r k) (otherIndices t)).prod,
    rightClearFactors_prod_mem t _, fun c ↦ ?_⟩
  rw [Units.val_mul, mul_rightClearFactors_apply (M : Matrix ι ι R') t _
    (otherIndices t) (otherIndices_nodup t)]
  by_cases hc : c = t
  · rw [hc, if_neg (fun h ↦ (mem_otherIndices_values_iff t t).1 h rfl), if_pos rfl, h1]
  · rw [if_pos ((mem_otherIndices_values_iff t c).2 hc), if_neg hc, h1, one_mul]
    exact add_neg_cancel _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinHorrocks_clear_of_eq_one

/-- **Moving a standard basis row.**  If row `r` is `e_s`, an elementary right factor turns it
into `e_r`. -/
theorem suslinHorrocks_move_single {R' : Type*} [Ring R'] (M : (Matrix ι ι R')ˣ) (r s : ι)
    (hrow : ∀ c : ι, (M : Matrix ι ι R') r c = if c = s then 1 else 0) :
    ∃ F ∈ elementaryGroup ι R',
      ∀ c : ι, ((M * F : (Matrix ι ι R')ˣ) : Matrix ι ι R') r c = if c = r then 1 else 0 := by
  by_cases hsr : s = r
  · refine ⟨1, Subgroup.one_mem _, fun c ↦ ?_⟩
    rw [mul_one, hrow c, hsr]
  · refine ⟨elementaryUnit s r hsr 1 * elementaryUnit r s (Ne.symm hsr) (-1),
      Subgroup.mul_mem _ (elementaryUnit_mem _ _ _ _) (elementaryUnit_mem _ _ _ _), fun c ↦ ?_⟩
    have h1 : ∀ c' : ι,
        ((M : Matrix ι ι R') * (elementaryUnit s r hsr 1 : (Matrix ι ι R')ˣ)) r c' =
          if c' = r then 1 else if c' = s then 1 else 0 := by
      intro c'
      rw [mul_elementaryUnit_apply, hrow r, hrow s, if_neg (Ne.symm hsr), if_pos rfl, mul_one,
        zero_add]
      by_cases hc' : c' = r
      · rw [if_pos hc', if_pos hc']
      · rw [if_neg hc', if_neg hc']
        exact hrow c'
    rw [← mul_assoc, Units.val_mul, Units.val_mul, mul_elementaryUnit_apply, h1 s, h1 r, h1 c,
      if_neg hsr, if_pos rfl, if_pos rfl]
    by_cases hc : c = s
    · have hcr : ¬ c = r := fun h ↦ hsr (hc.symm.trans h)
      rw [if_pos hc, if_neg hcr, one_mul]
      exact add_neg_cancel _
    · rw [if_neg hc, if_neg hc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinHorrocks_move_single

/-- **Two column additions into column `e`.**  Right multiplication by `x_{c e}(a₁)` and then
`x_{t e}(a₂)` changes entry `(r, e)` to `M r e + M r c * a₁ + M r t * a₂`. -/
theorem suslinHorrocks_two_col_apply {R' : Type*} [Ring R'] (M : Matrix ι ι R') (r c t e : ι)
    (hce : c ≠ e) (hte : t ≠ e) (a₁ a₂ : R') :
    (M * ((elementaryUnit c e hce a₁ : (Matrix ι ι R')ˣ) : Matrix ι ι R') *
        ((elementaryUnit t e hte a₂ : (Matrix ι ι R')ˣ) : Matrix ι ι R')) r e =
      M r e + M r c * a₁ + M r t * a₂ := by
  rw [mul_elementaryUnit_apply (M * ((elementaryUnit c e hce a₁ : (Matrix ι ι R')ˣ) :
      Matrix ι ι R')) t e hte a₂ r e, if_pos rfl,
    mul_elementaryUnit_apply M c e hce a₁ r e, mul_elementaryUnit_apply M c e hce a₁ r t,
    if_pos rfl, if_neg hte]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinHorrocks_two_col_apply

/-- **A unimodular row is not a unit modulo `𝔪` at a monic entry of positive degree.**  Over a
local ring, if the entry of row `r` at `t` is monic of positive degree, some other entry of the
row is nonzero modulo the maximal ideal.  Otherwise the row identity `∑ M r c · M⁻¹ c r = 1`
reduces to `f̄ · ḡ = 1` over the residue field, so `f̄` would be a unit of positive degree. -/
theorem suslinHorrocks_exists_residue_ne_zero [IsLocalRing R] (M : (Matrix ι ι (Polynomial R))ˣ)
    (r t : ι) (ht : ((M : Matrix ι ι (Polynomial R)) r t).Monic)
    (hd : 0 < ((M : Matrix ι ι (Polynomial R)) r t).natDegree) :
    ∃ c : ι, c ≠ t ∧
      ((M : Matrix ι ι (Polynomial R)) r c).map (IsLocalRing.residue R) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hsum : ((M : Matrix ι ι (Polynomial R)) *
      ((M⁻¹ : (Matrix ι ι (Polynomial R))ˣ) : Matrix ι ι (Polynomial R))) r r = 1 := by
    rw [Units.mul_inv, Matrix.one_apply_eq]
  rw [Matrix.mul_apply] at hsum
  have hmap := congrArg (Polynomial.mapRingHom (IsLocalRing.residue R)) hsum
  have hzero : ∀ c : ι, c ≠ t →
      Polynomial.mapRingHom (IsLocalRing.residue R) ((M : Matrix ι ι (Polynomial R)) r c *
        ((M⁻¹ : (Matrix ι ι (Polynomial R))ˣ) : Matrix ι ι (Polynomial R)) c r) = 0 := by
    intro c hc
    rw [map_mul, Polynomial.coe_mapRingHom, hcon c hc, zero_mul]
  rw [map_sum, map_one, Fintype.sum_eq_single t hzero, map_mul,
    Polynomial.coe_mapRingHom] at hmap
  have hunit : IsUnit (((M : Matrix ι ι (Polynomial R)) r t).map (IsLocalRing.residue R)) :=
    IsUnit.of_mul_eq_one _ hmap
  have h0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
  rw [ht.natDegree_map (IsLocalRing.residue R)] at h0
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinHorrocks_exists_residue_ne_zero

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
