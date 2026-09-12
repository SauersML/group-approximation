import GroupApproximation.Sofic.CyclicStack
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Countable windows and cyclic level schedules

This file contains the diagonal bookkeeping used by locally-residually-finite
by integer compression models.  It is independent of the group action and of
the residual packet chosen at each stage.

For a countable nonempty type `G`, `exhaustion G n` consists of the first
`n + 1` values of a fixed surjection `ℕ → G`, together with a distinguished
base point.  The cyclic level size is also `n + 1`.  At this size, the fraction
of levels at which translation by a fixed integer wraps around tends to zero;
the same is true after taking a square root.
-/

namespace GroupApproximation
namespace LocallyRFByIntSchedule

open Filter SoficIntegerExtension

noncomputable section

universe u

variable (G : Type u) [Nonempty G] [Countable G]

/-! ## A canonical finite exhaustion -/

/-- A fixed surjection from the natural numbers onto a countable nonempty
type. -/
noncomputable def enumerate : ℕ → G :=
  Classical.choose (exists_surjective_nat G)

theorem enumerate_surjective : Function.Surjective (enumerate G) :=
  Classical.choose_spec (exists_surjective_nat G)

/-- The first `n + 1` enumerated points, with a distinguished point inserted.
For a group the distinguished point will be `1`. -/
noncomputable def exhaustion (base : G) (n : ℕ) : Finset G := by
  classical
  exact insert base ((Finset.range (n + 1)).image (enumerate G))

@[simp] theorem base_mem_exhaustion (base : G) (n : ℕ) :
    base ∈ exhaustion G base n := by
  classical
  simp [exhaustion]

/-- The finite windows increase with the stage. -/
theorem exhaustion_mono (base : G) {m n : ℕ} (hmn : m ≤ n) :
    exhaustion G base m ⊆ exhaustion G base n := by
  classical
  refine Finset.insert_subset_insert _ (Finset.image_subset_image ?_)
  intro i hi
  simp only [Finset.mem_range] at hi ⊢
  omega

/-- Every point belongs to every sufficiently late finite window. -/
theorem eventually_mem_exhaustion (base : G) (g : G) :
    ∃ N : ℕ, ∀ n ≥ N, g ∈ exhaustion G base n := by
  obtain ⟨i, hi⟩ := enumerate_surjective G g
  refine ⟨i, fun n hn ↦ exhaustion_mono G base hn ?_⟩
  classical
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨i, Finset.self_mem_range_succ i, hi⟩)

/-- Filter form of eventual exhaustion. -/
theorem eventually_eventually_mem_exhaustion (base : G) (g : G) :
    ∀ᶠ n in atTop, g ∈ exhaustion G base n := by
  obtain ⟨N, hN⟩ := eventually_mem_exhaustion G base g
  exact Filter.eventually_atTop.mpr ⟨N, hN⟩

/-! ## The cyclic level schedule -/

/-- Stage `n` uses `n + 1` cyclic levels. -/
def levelSize (n : ℕ) : ℕ := n + 1

instance levelSize_neZero (n : ℕ) : NeZero (levelSize n) :=
  ⟨by simp [levelSize]⟩

theorem levelSize_pos (n : ℕ) : 0 < levelSize n := by
  simp [levelSize]

/-- The honest integer representatives of the cyclic levels at stage `n`. -/
noncomputable def levelWindow (n : ℕ) : Finset ℤ := by
  classical
  exact (Finset.range (levelSize n)).image fun j : ℕ ↦ (j : ℤ)

theorem natCast_mem_levelWindow {n j : ℕ} (hj : j < levelSize n) :
    (j : ℤ) ∈ levelWindow n := by
  classical
  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩

theorem zmodVal_mem_levelWindow (n : ℕ) (j : ZMod (levelSize n)) :
    (j.val : ℤ) ∈ levelWindow n :=
  natCast_mem_levelWindow (ZMod.val_lt j)

/-! ## Boundary ratios -/

/-- The fraction of cyclic levels at which addition by `q` wraps around. -/
noncomputable def boundaryRatio (q : ℤ) (n : ℕ) : ℝ :=
  (badLevels (levelSize n) q).card / (levelSize n : ℝ)

theorem boundaryRatio_nonneg (q : ℤ) (n : ℕ) :
    0 ≤ boundaryRatio q n := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The uniform `2 |q| / (n + 1)` estimate for the wrap-around fraction. -/
theorem boundaryRatio_le (q : ℤ) (n : ℕ) :
    boundaryRatio q n ≤
      (2 * (q.natAbs : ℝ)) / (levelSize n : ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast card_badLevels_le (L := levelSize n) q

/-- For each fixed integer shift, the wrap-around fraction tends to zero. -/
theorem tendsto_boundaryRatio (q : ℤ) :
    Tendsto (boundaryRatio q) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall (boundaryRatio_nonneg q)
  · exact Eventually.of_forall (boundaryRatio_le q)
  · simpa [levelSize, div_eq_mul_inv, mul_assoc] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (2 * (q.natAbs : ℝ))

/-- The square root of the boundary fraction also tends to zero. -/
theorem tendsto_sqrt_boundaryRatio (q : ℤ) :
    Tendsto (fun n ↦ Real.sqrt (boundaryRatio q n)) atTop (nhds 0) := by
  have hsqrt : Tendsto Real.sqrt (nhds (0 : ℝ)) (nhds 0) :=
    Real.continuous_sqrt.tendsto' 0 0 Real.sqrt_zero
  exact hsqrt.comp (tendsto_boundaryRatio q)

/-! ## A generic height function -/

/-- Boundary ratio attached to a point through an arbitrary integer-valued
height function. -/
noncomputable def heightBoundaryRatio {G : Type u} (height : G → ℤ)
    (g : G) (n : ℕ) : ℝ :=
  boundaryRatio (height g) n

theorem tendsto_heightBoundaryRatio {G : Type u} (height : G → ℤ) (g : G) :
    Tendsto (heightBoundaryRatio height g) atTop (nhds 0) :=
  tendsto_boundaryRatio (height g)

theorem tendsto_sqrt_heightBoundaryRatio {G : Type u}
    (height : G → ℤ) (g : G) :
    Tendsto (fun n ↦ Real.sqrt (heightBoundaryRatio height g n))
      atTop (nhds 0) :=
  tendsto_sqrt_boundaryRatio (height g)

end

end LocallyRFByIntSchedule
end GroupApproximation
