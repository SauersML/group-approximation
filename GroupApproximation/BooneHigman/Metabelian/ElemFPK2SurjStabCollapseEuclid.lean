import GroupApproximation.BooneHigman.Metabelian.ElemFPK2SurjStabCollapseReach
import GroupApproximation.Meta.AxiomGuard

/-!
# Surjective `K₂` stability, rank-two collapse: Euclid away from `i` (lane bh-met-89)

`surjStabCollapse_away_reach`: for `i ≠ k₀` in `Fin n`, every row `w ∈ ℤ[1/m]^n` can be moved,
by an element of `St_n(ℤ[1/m])` fixing the row `e_i β` and the column `e_i γ`
(`SurjStabCollapseFix`), to `e_i (w i) + e_k δ` for some `k ≠ i`.

Truth check.  Clear denominators: `w = s · w₀` with `w₀ ∈ ℤ^n`.  Run Euclid on the
coordinates other than `i` only, with the moves `w ↦ w + e_l (w_j q)`, `j ≠ l`, `j, l ≠ i`
(`surjStabCollapse_int_step`).  If `0 < |w₀ j| ≤ |w₀ l|`, replace `w₀ l` by `w₀ l % w₀ j`.
This lowers `∑ |w₀ k|` strictly and leaves coordinate `i` unchanged.  When no such pair
exists, at most one coordinate `k ≠ i` is nonzero (`surjStabCollapse_int_supp`).  This is
the argument of `ElemFPK2SurjStabGaussEuclid` on `n - 1 ≥ 1` coordinates.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open scoped Matrix
open GroupApproximation.SteinbergGroup GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

variable {R : Type*} [Ring R] {n : ℕ}

/-- Euclid away from `i` on an integral row `s · w₀`, by induction on `∑ |w₀ k|`. -/
theorem surjStabCollapse_int_reach (i k0 : Fin n) (hk0 : k0 ≠ i) (s : R) (N : ℕ) :
    ∀ w0 : Fin n → ℤ, ∑ k, (w0 k).natAbs = N →
      ∃ (k : Fin n) (δ : R), k ≠ i ∧ SurjStabCollapseReach i (fun k => s * ((w0 k : ℤ) : R))
        (Pi.single i (s * ((w0 i : ℤ) : R)) + Pi.single k δ) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro w0 hN
    by_cases hex : ∃ j l : Fin n, j ≠ l ∧ j ≠ i ∧ l ≠ i ∧ w0 j ≠ 0 ∧
        (w0 j).natAbs ≤ (w0 l).natAbs
    · obtain ⟨j, l, hjl, hji, hli, hj, hle⟩ := hex
      have hl1 : (w0 + Pi.single l (w0 j * -(w0 l / w0 j))) l = w0 l % w0 j := by
        rw [Pi.add_apply, Pi.single_eq_same, Int.emod_def]
        ring
      have hlt : (w0 l % w0 j).natAbs < (w0 l).natAbs := by
        have h0 := Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.emod_nonneg (w0 l) hj)
          (Int.emod_lt_abs (w0 l) hj)
        rw [Int.natAbs_abs] at h0
        exact lt_of_lt_of_le h0 hle
      have hsum : ∑ k, ((w0 + Pi.single l (w0 j * -(w0 l / w0 j))) k).natAbs <
          ∑ k, (w0 k).natAbs := by
        refine Finset.sum_lt_sum (fun k _ => ?_) ⟨l, Finset.mem_univ l, by rw [hl1]; exact hlt⟩
        by_cases hk : k = l
        · rw [hk, hl1]
          exact hlt.le
        · exact le_of_eq (by rw [Pi.add_apply, Pi.single_eq_of_ne hk, add_zero])
      have hi : (w0 + Pi.single l (w0 j * -(w0 l / w0 j))) i = w0 i := by
        rw [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hli), add_zero]
      obtain ⟨k, δ, hki, hr⟩ := ih _ (lt_of_lt_of_eq hsum hN)
        (w0 + Pi.single l (w0 j * -(w0 l / w0 j))) rfl
      rw [hi] at hr
      exact ⟨k, δ, hki,
        surjStabCollapse_reach_trans (surjStabCollapse_int_step s w0 i j l hjl hji hli _) hr⟩
    · obtain ⟨k, hki, hk⟩ := surjStabCollapse_int_supp i k0 hk0 w0 hex
      refine ⟨k, s * ((w0 k : ℤ) : R), hki, 1, surjStabCollapse_fix_one i, ?_⟩
      rw [map_one padMat, Matrix.vecMul_one]
      funext l
      rw [Pi.add_apply]
      show s * ((w0 l : ℤ) : R) =
        Pi.single i (s * ((w0 i : ℤ) : R)) l + Pi.single k (s * ((w0 k : ℤ) : R)) l
      by_cases hli : l = i
      · rw [hli, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hki), add_zero]
      · by_cases hlk : l = k
        · rw [hlk, Pi.single_eq_same, Pi.single_eq_of_ne hki, zero_add]
        · rw [Pi.single_eq_of_ne hli, Pi.single_eq_of_ne hlk, add_zero, hk l hli hlk,
            Int.cast_zero, mul_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabCollapse_int_reach

/-- Euclid away from `i` over `ℤ[1/m]`: `w` reaches `e_i (w i) + e_k δ` with `k ≠ i`, by an
element fixing `e_i`. -/
theorem surjStabCollapse_away_reach {m : ℕ} (i k0 : Fin n) (hk0 : k0 ≠ i)
    (w : Fin n → Localization.Away (m : ℤ)) :
    ∃ (k : Fin n) (δ : Localization.Away (m : ℤ)), k ≠ i ∧
      SurjStabCollapseReach i w (Pi.single i (w i) + Pi.single k δ) := by
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
  obtain ⟨k, δ, hki, hr⟩ := surjStabCollapse_int_reach i k0 hk0
    (↑hu.unit⁻¹ : Localization.Away (m : ℤ)) (∑ k, (w0 k).natAbs) w0 rfl
  refine ⟨k, δ, hki, ?_⟩
  rw [hw]
  exact hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.surjStabCollapse_away_reach

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
