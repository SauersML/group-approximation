import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.StandardCoord
import GroupApproximation.Meta.AxiomGuard

/-!
# Kasparov stabilization, lane `nm-tww-16`: `H_B` is complete

`isCompleteModule_standard`: every Cauchy sequence of `H_B = standardModule ℕ B` has a
limit.

The proof follows the usual `ℓ²` argument. Each coordinate is Cauchy in `B`, which is
complete, so it has a limit `g i`. Every finite partial sum of `‖g - u n‖²` is a limit
of partial sums of `‖u m - u n‖²`, which gives the bound `ε²` (`partial_le`). The
triangle inequality in `Bᵗ` (`psqrt_add_le`) turns that bound into the Cauchy criterion
for `∑ g⋆g` (`summable_limit`). Letting the finite set grow gives `‖g - u n‖ ≤ ε`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KasparovStab

open GroupApproximation.HilbertModule Filter Topology

universe v

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem coe_sub_apply (f g : (standardModule ℕ B).carrier) (i : ℕ) :
    (f - g).1 i = f.1 i - g.1 i := rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.coe_sub_apply

/-- The coordinates of a Cauchy sequence are Cauchy. -/
theorem coord_cauchySeq {u : ℕ → (standardModule ℕ B).carrier}
    (hu : IsCauchy (standardModule ℕ B) u) (i : ℕ) :
    CauchySeq fun n => (u n).1 i := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hu (ε / 2) (half_pos hε)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  show ‖(u m - u n).1 i‖ < ε
  calc ‖(u m - u n).1 i‖ ≤ (standardModule ℕ B).norm (u m - u n) := norm_coord_le _ i
    _ ≤ ε / 2 := hN m n hm hn
    _ < ε := half_lt_self hε

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.coord_cauchySeq

/-- **The partial estimate.** Every finite partial sum of `‖g - u n‖²` is at most `ε²`
once `n` is past the Cauchy index for `ε`. -/
theorem partial_le {u : ℕ → (standardModule ℕ B).carrier} {g : ℕ → B}
    (hg : ∀ i, Tendsto (fun n => (u n).1 i) atTop (𝓝 (g i))) {ε : ℝ} {N : ℕ}
    (hN : ∀ m n : ℕ, N ≤ m → N ≤ n → (standardModule ℕ B).norm (u m - u n) ≤ ε)
    {n : ℕ} (hn : N ≤ n) (t : Finset ℕ) :
    ‖∑ i ∈ t, star (g i - (u n).1 i) * (g i - (u n).1 i)‖ ≤ ε ^ 2 := by
  have hbound : ∀ m : ℕ, N ≤ m →
      ‖∑ i ∈ t, star ((u m).1 i - (u n).1 i) * ((u m).1 i - (u n).1 i)‖ ≤ ε ^ 2 := by
    intro m hm
    have hsum := summable_coe (u m - u n)
    have hle : ∑ i ∈ t, star ((u m - u n).1 i) * (u m - u n).1 i
        ≤ ∑' i, star ((u m - u n).1 i) * (u m - u n).1 i :=
      hsum.sum_le_tsum t fun i _ => star_mul_self_nonneg _
    have hnorm := OrderZero.norm_le_norm_of_nonneg_of_le
      (Finset.sum_nonneg fun i _ => star_mul_self_nonneg ((u m - u n).1 i)) hle
    have hsq := (standardModule ℕ B).norm_sq (u m - u n)
    rw [standardModule_inner] at hsq
    have hpow := pow_le_pow_left₀ ((standardModule ℕ B).norm_nonneg (u m - u n))
      (hN m n hm hn) 2
    exact le_trans hnorm (hsq.symm.trans_le hpow)
  have hT : Tendsto
      (fun m => ‖∑ i ∈ t, star ((u m).1 i - (u n).1 i) * ((u m).1 i - (u n).1 i)‖)
      atTop (𝓝 ‖∑ i ∈ t, star (g i - (u n).1 i) * (g i - (u n).1 i)‖) := by
    refine Tendsto.norm (tendsto_finsetSum t fun i _ => ?_)
    have hi : Tendsto (fun m => (u m).1 i - (u n).1 i) atTop (𝓝 (g i - (u n).1 i)) :=
      (hg i).sub tendsto_const_nhds
    exact hi.star.mul hi
  exact le_of_tendsto hT (eventually_atTop.mpr ⟨N, hbound⟩)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.partial_le

/-- The coordinatewise limit of a Cauchy sequence is square-summable. -/
theorem summable_limit {u : ℕ → (standardModule ℕ B).carrier}
    (hu : IsCauchy (standardModule ℕ B) u) {g : ℕ → B}
    (hg : ∀ i, Tendsto (fun n => (u n).1 i) atTop (𝓝 (g i))) :
    Summable fun i => star (g i) * g i := by
  rw [summable_iff_vanishing_norm]
  intro ε hε
  have hδ : 0 < Real.sqrt ε / 2 := half_pos (Real.sqrt_pos.mpr hε)
  obtain ⟨N, hN⟩ := hu (Real.sqrt ε / 2) hδ
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp (summable_coe (u N))
    ((Real.sqrt ε / 2) ^ 2) (pow_pos hδ 2)
  refine ⟨s, fun t ht => ?_⟩
  have ha : Real.sqrt ‖∑ i ∈ t, star (g i - (u N).1 i) * (g i - (u N).1 i)‖
      ≤ Real.sqrt ε / 2 :=
    (Real.sqrt_le_left hδ.le).mpr (partial_le hg hN le_rfl t)
  have hb : Real.sqrt ‖∑ i ∈ t, star ((u N).1 i) * (u N).1 i‖ < Real.sqrt ε / 2 :=
    (Real.sqrt_lt' hδ).mpr (hs t ht)
  have htri := psqrt_add_le t (fun i => g i - (u N).1 i) (fun i => (u N).1 i)
  simp only [sub_add_cancel] at htri
  have hlt : Real.sqrt ‖∑ i ∈ t, star (g i) * g i‖ < Real.sqrt ε := by
    calc Real.sqrt ‖∑ i ∈ t, star (g i) * g i‖
        ≤ Real.sqrt ‖∑ i ∈ t, star (g i - (u N).1 i) * (g i - (u N).1 i)‖
          + Real.sqrt ‖∑ i ∈ t, star ((u N).1 i) * (u N).1 i‖ := htri
      _ < Real.sqrt ε / 2 + Real.sqrt ε / 2 := add_lt_add_of_le_of_lt ha hb
      _ = Real.sqrt ε := add_halves _
  exact (Real.sqrt_lt_sqrt_iff (norm_nonneg _)).mp hlt

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.summable_limit

/-- **`H_B` is complete.** -/
theorem isCompleteModule_standard : IsCompleteModule (standardModule ℕ B) := by
  intro u hu
  choose g hg using fun i => cauchySeq_tendsto_of_complete (coord_cauchySeq hu i)
  have hsum : Summable fun i => star (g i) * g i := summable_limit hu hg
  let gH : (standardModule ℕ B).carrier := ⟨g, hsum⟩
  refine ⟨gH, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hu ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [modNorm_sub_comm, standardModule_norm]
  have hT := (summable_coe (gH - u n)).tendsto_sum_tsum_nat.norm
  have hle : ‖∑' i, star ((gH - u n).1 i) * (gH - u n).1 i‖ ≤ ε ^ 2 := by
    refine le_of_tendsto hT (Eventually.of_forall fun k => ?_)
    exact partial_le hg hN hn (Finset.range k)
  calc Real.sqrt ‖∑' i, star ((gH - u n).1 i) * (gH - u n).1 i‖
      ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hle
    _ = ε := Real.sqrt_sq hε.le

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.isCompleteModule_standard

end KasparovStab
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
