import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabGaussMove
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjective `K₂` stability: Euclid on the middle row (lane bh-met-82)

`surjStabGauss_away_reach_single`: every row `w ∈ ℤ[1/m]^n` (`n > 0`) can be moved by the
right action of `St_n(ℤ[1/m])` (through `padMat`) to `Pi.single i β`.

Truth check.  Clear denominators: `w = s⁻¹ · w₀` with `s = b ∈ powers m` and `w₀ ∈ ℤ^n`.  Run
Euclid with the column operations `w ↦ w + e_j (w_i q)` of `surjStabGauss_reach_step`.
Whenever two nonzero coordinates satisfy `0 < |w₀ i| ≤ |w₀ j|`, replace `w₀ j` by
`w₀ j % w₀ i` (take `q = -(w₀ j / w₀ i)`).  This lowers `∑ |w₀ k|` strictly, since
`|w₀ j % w₀ i| < |w₀ i| ≤ |w₀ j|`.  When no such pair exists, at most one coordinate is
nonzero, so `w₀` is a single.  The scalar `s⁻¹` rides along, because the column operations are
`R`-linear on the left.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

variable {R : Type*} [Ring R] {n : ℕ}

/-- One integral column step on a row `s · w₀`. -/
theorem surjStabGauss_int_step (s : R) (w0 : Fin n → ℤ) (i j : Fin n) (hij : i ≠ j) (q : ℤ) :
    SurjStabGaussReach (fun k => s * ((w0 k : ℤ) : R))
      (fun k => s * (((w0 + Pi.single j (w0 i * q)) k : ℤ) : R)) := by
  obtain ⟨h, hh⟩ := surjStabGauss_reach_step (fun k => s * ((w0 k : ℤ) : R)) i j hij (q : R)
  refine ⟨h, hh.trans ?_⟩
  funext k
  by_cases hk : k = j
  · subst hk
    simp only [Pi.add_apply, Pi.single_eq_same, Int.cast_add, Int.cast_mul, mul_add, mul_assoc]
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hk, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabGauss_int_step

/-- If no two distinct nonzero coordinates exist, `w₀` is supported at one index. -/
theorem surjStabGauss_int_supp (hn : 0 < n) (w0 : Fin n → ℤ)
    (hex : ¬∃ i j : Fin n, i ≠ j ∧ w0 i ≠ 0 ∧ (w0 i).natAbs ≤ (w0 j).natAbs) :
    ∃ i : Fin n, ∀ k, k ≠ i → w0 k = 0 := by
  by_cases hall : ∃ i, w0 i ≠ 0
  · obtain ⟨i, hi⟩ := hall
    refine ⟨i, fun k hk => ?_⟩
    by_contra hk0
    rcases le_total (w0 i).natAbs (w0 k).natAbs with hle | hle
    · exact hex ⟨i, k, fun e => hk e.symm, hi, hle⟩
    · exact hex ⟨k, i, hk, hk0, hle⟩
  · refine ⟨⟨0, hn⟩, fun k _ => ?_⟩
    by_contra hk0
    exact hall ⟨k, hk0⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabGauss_int_supp

/-- Euclid: every integral row `s · w₀` reaches a single, by induction on `∑ |w₀ k|`. -/
theorem surjStabGauss_int_reach (hn : 0 < n) (s : R) (N : ℕ) :
    ∀ w0 : Fin n → ℤ, ∑ k, (w0 k).natAbs = N →
      ∃ (i : Fin n) (β : R), SurjStabGaussReach (fun k => s * ((w0 k : ℤ) : R)) (Pi.single i β) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro w0 hN
    by_cases hex : ∃ i j : Fin n, i ≠ j ∧ w0 i ≠ 0 ∧ (w0 i).natAbs ≤ (w0 j).natAbs
    · obtain ⟨i, j, hij, hi, hle⟩ := hex
      have hj1 : (w0 + Pi.single j (w0 i * -(w0 j / w0 i))) j = w0 j % w0 i := by
        rw [Pi.add_apply, Pi.single_eq_same, Int.emod_def, mul_neg, ← sub_eq_add_neg]
      have hlt : (w0 j % w0 i).natAbs < (w0 j).natAbs := by
        have h0 := Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.emod_nonneg (w0 j) hi)
          (Int.emod_lt_abs (w0 j) hi)
        rw [Int.natAbs_abs] at h0
        exact lt_of_lt_of_le h0 hle
      have hsum : ∑ k, ((w0 + Pi.single j (w0 i * -(w0 j / w0 i))) k).natAbs <
          ∑ k, (w0 k).natAbs := by
        refine Finset.sum_lt_sum (fun k _ => ?_) ⟨j, Finset.mem_univ j, by rw [hj1]; exact hlt⟩
        by_cases hk : k = j
        · rw [hk, hj1]
          exact hlt.le
        · rw [Pi.add_apply, Pi.single_eq_of_ne hk, add_zero]
      obtain ⟨i', β, hr⟩ := ih _ (lt_of_lt_of_eq hsum hN)
        (w0 + Pi.single j (w0 i * -(w0 j / w0 i))) rfl
      exact ⟨i', β, surjStabGauss_reach_trans (surjStabGauss_int_step s w0 i j hij _) hr⟩
    · obtain ⟨i, hi⟩ := surjStabGauss_int_supp hn w0 hex
      refine ⟨i, s * ((w0 i : ℤ) : R), 1, ?_⟩
      rw [map_one, Matrix.vecMul_one]
      funext k
      by_cases hk : k = i
      · rw [hk, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hk, hi k hk, Int.cast_zero, mul_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabGauss_int_reach

/-- Every row over `ℤ[1/m]` reaches a single under the right `St_n` action. -/
theorem surjStabGauss_away_reach_single {m : ℕ} (hn : 0 < n)
    (w : Fin n → Localization.Away (m : ℤ)) :
    ∃ (i : Fin n) (β : Localization.Away (m : ℤ)), SurjStabGaussReach w (Pi.single i β) := by
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers (m : ℤ)) w
  choose w0 hw0 using fun k => RingHom.mem_rangeS.mp (hb k)
  have hu : IsUnit (algebraMap ℤ (Localization.Away (m : ℤ)) (b : ℤ)) :=
    IsLocalization.map_units (Localization.Away (m : ℤ)) b
  have hw : w = fun k => (↑hu.unit⁻¹ : Localization.Away (m : ℤ)) *
      ((w0 k : ℤ) : Localization.Away (m : ℤ)) := by
    funext k
    rw [← eq_intCast (algebraMap ℤ (Localization.Away (m : ℤ))) (w0 k), hw0 k, Algebra.smul_def,
      ← mul_assoc, hu.val_inv_mul, one_mul]
  obtain ⟨i, β, hr⟩ := surjStabGauss_int_reach hn (↑hu.unit⁻¹ : Localization.Away (m : ℤ))
    (∑ k, (w0 k).natAbs) w0 rfl
  refine ⟨i, β, ?_⟩
  rw [hw]
  exact hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabGauss_away_reach_single

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
