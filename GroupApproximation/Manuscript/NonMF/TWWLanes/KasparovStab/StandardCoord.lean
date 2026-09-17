import GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.Approx
import GroupApproximation.Meta.AxiomGuard

/-!
# Kasparov stabilization, lane `nm-tww-16`: coordinates of `H_B`

These are elementary facts about `H_B = standardModule ℕ B` used by the completeness
proof and by the Mingo--Phillips operator.

* `norm_coord_le`: `‖f i‖ ≤ ‖f‖`.
* `psqrt_add_le`: the triangle inequality for `√‖∑_{i∈t} x_i⋆x_i‖`, taken from the
  finite direct sum `piSelf t B`.
* `coe_sum_apply`: coordinates of a finite sum in `H_B`.
* `single n a`, its coordinates and its norm.
* `truncate_eq_sum`: a truncation is a finite sum of singles.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KasparovStab

open GroupApproximation.HilbertModule

universe v

variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A coordinate is bounded by the norm of the vector. -/
theorem norm_coord_le (f : (standardModule ℕ B).carrier) (i : ℕ) :
    ‖f.1 i‖ ≤ (standardModule ℕ B).norm f := by
  have hle : star (f.1 i) * f.1 i ≤ ∑' j, star (f.1 j) * f.1 j :=
    le_hasSum (summable_coe f).hasSum i fun j _ => star_mul_self_nonneg _
  have hn : ‖star (f.1 i) * f.1 i‖ ≤ ‖∑' j, star (f.1 j) * f.1 j‖ :=
    OrderZero.norm_le_norm_of_nonneg_of_le (star_mul_self_nonneg (f.1 i)) hle
  rw [CStarRing.norm_star_mul_self] at hn
  rw [standardModule_norm]
  calc ‖f.1 i‖ = Real.sqrt (‖f.1 i‖ * ‖f.1 i‖) :=
        (Real.sqrt_mul_self (norm_nonneg (f.1 i))).symm
    _ ≤ Real.sqrt ‖∑' j, star (f.1 j) * f.1 j‖ := Real.sqrt_le_sqrt hn

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.norm_coord_le

/-- The norm of a restriction to a finite set, read in `piSelf t B`. -/
theorem pnorm_eq (t : Finset ℕ) (a : ℕ → B) :
    (piSelf (↥t) B).norm (fun i : ↥t => a (i : ℕ))
      = Real.sqrt ‖∑ i ∈ t, star (a i) * a i‖ := by
  rw [CStarModule.norm_def]
  congr 1
  show ‖∑ i : ↥t, star (a (i : ℕ)) * a (i : ℕ)‖ = ‖∑ i ∈ t, star (a i) * a i‖
  rw [← Finset.sum_coe_sort t]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.pnorm_eq

/-- The triangle inequality for finite partial sums. -/
theorem psqrt_add_le (t : Finset ℕ) (a b : ℕ → B) :
    Real.sqrt ‖∑ i ∈ t, star (a i + b i) * (a i + b i)‖
      ≤ Real.sqrt ‖∑ i ∈ t, star (a i) * a i‖ + Real.sqrt ‖∑ i ∈ t, star (b i) * b i‖ := by
  calc Real.sqrt ‖∑ i ∈ t, star (a i + b i) * (a i + b i)‖
      = (piSelf (↥t) B).norm (fun i : ↥t => a (i : ℕ) + b (i : ℕ)) :=
        (pnorm_eq t (fun i => a i + b i)).symm
    _ ≤ (piSelf (↥t) B).norm (fun i : ↥t => a (i : ℕ))
          + (piSelf (↥t) B).norm (fun i : ↥t => b (i : ℕ)) :=
        (piSelf (↥t) B).norm_add_le (fun i : ↥t => a (i : ℕ)) (fun i : ↥t => b (i : ℕ))
    _ = Real.sqrt ‖∑ i ∈ t, star (a i) * a i‖ + Real.sqrt ‖∑ i ∈ t, star (b i) * b i‖ := by
        rw [pnorm_eq t a, pnorm_eq t b]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.psqrt_add_le

/-- Coordinates of a finite sum in `H_B`. -/
theorem coe_sum_apply {ι : Type*} (s : Finset ι) (g : ι → (standardModule ℕ B).carrier)
    (j : ℕ) : (∑ i ∈ s, g i).1 j = ∑ i ∈ s, (g i).1 j := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty] <;> rfl
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih] <;> rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.coe_sum_apply

/-- The vector of `H_B` with `a` in coordinate `n` and `0` elsewhere. -/
noncomputable def single (n : ℕ) (a : B) : (standardModule ℕ B).carrier :=
  ⟨fun i => if i = n then a else 0, by
    show Summable fun i => star (if i = n then a else 0) * (if i = n then a else 0)
    refine summable_of_ne_finset_zero (s := {n}) fun i hi => ?_
    have hin : i ≠ n := fun h => hi (Finset.mem_singleton.mpr h)
    simp [hin]⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.single

theorem single_coe (n : ℕ) (a : B) (i : ℕ) :
    (single n a).1 i = if i = n then a else 0 := rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.single_coe

theorem single_coe_self (n : ℕ) (a : B) : (single n a).1 n = a := by
  rw [single_coe, if_pos rfl]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.single_coe_self

theorem single_coe_of_ne {n i : ℕ} (a : B) (h : i ≠ n) : (single n a).1 i = 0 := by
  rw [single_coe, if_neg h]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.single_coe_of_ne

theorem norm_single (n : ℕ) (a : B) : (standardModule ℕ B).norm (single n a) = ‖a‖ := by
  have h0 : ∀ i, i ≠ n → star ((single n a).1 i) * (single n a).1 i = 0 := by
    intro i hi
    rw [single_coe_of_ne a hi, star_zero, zero_mul]
  rw [standardModule_norm, tsum_eq_single n h0, single_coe_self,
    CStarRing.norm_star_mul_self, Real.sqrt_mul_self (norm_nonneg a)]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.norm_single

/-- A truncation is the finite sum of its singles. -/
theorem truncate_eq_sum (s : Finset ℕ) (f : (standardModule ℕ B).carrier) :
    (truncate s f : (standardModule ℕ B).carrier) = ∑ i ∈ s, single i (f.1 i) := by
  refine Subtype.ext (funext fun j => ?_)
  rw [coe_sum_apply]
  by_cases hj : j ∈ s
  · rw [truncate_coe_of_mem hj, Finset.sum_eq_single j]
    · rw [single_coe_self]
    · intro i _ hij
      exact single_coe_of_ne _ (Ne.symm hij)
    · intro h
      exact absurd hj h
  · rw [truncate_coe_of_not_mem hj]
    refine (Finset.sum_eq_zero fun i hi => ?_).symm
    have hji : j ≠ i := fun h => hj (h ▸ hi)
    exact single_coe_of_ne _ hji

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KasparovStab.truncate_eq_sum

end KasparovStab
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
