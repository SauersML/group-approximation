import GroupApproximation.Analysis.ShulmanFillNormingTailAsymptotic

/-!
# Truncating a tail lift past its cut

The gluing of `Analysis/ShulmanFillNormingGluing` sends two lifts of `D` to one
representation of the amalgam in the reduced product `∏_t 𝒟 / ⨁_t 𝒟`, and it is
a `*`-homomorphism there because each defect vanishes *in the norm of `𝒟`*,
which is the supremum over coordinates.  A `StarStrongTailLift` does not supply
that: past the cut its defects are small, below the cut they are unconstrained,
and the supremum sees both.

The bridge is to truncate.  Multiplying by the projection that is `1` past the
cut and `0` below leaves every defect small *and* makes it small in the
supremum, because the truncated defect is zero where it was uncontrolled.

## What truncation costs

Exactly one clause, and it is the interesting one.  Four of the five defects
survive truncation, because truncation is a `*`-homomorphism: the truncated
defect of `b, c` is the truncation of the defect of `b, c`.  The unit clause
does not: the truncated family sends `1` to the projection rather than to `1`,
and `‖cutProj c - 1‖ = 1` whenever `c > 0`.

That is not an accident of the construction and it cannot be repaired by
truncating differently.  Filling the coordinates below the cut with anything
exactly multiplicative and unital would be a finite-dimensional representation
of `B`, and `Analysis/ShulmanFillNormingPrintedPairCharacter` is the observation
that a separable MF algebra need not have one.  So a glued map built from a tail
lift is unital into the corner cut out by the projections, not into the whole
reduced product --- which is where the gluing has to be re-aimed.
-/

namespace GroupApproximation
namespace ShulmanFill

open Filter Topology

noncomputable section

universe u

section Truncation

variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]

/-- The projection of the bounded product onto the coordinates past a cut. -/
def cutProj (c : ℕ) : StarStrong.BoundedStarSequence A :=
  ⟨fun n ↦ if c ≤ n then 1 else 0, memℓp_infty ⟨1, by
    rintro _ ⟨n, rfl⟩
    by_cases h : c ≤ n
    · simp only [if_pos h]
      exact le_of_eq norm_one
    · simp only [if_neg h, norm_zero]
      exact zero_le_one⟩⟩

@[simp] theorem cutProj_apply (c n : ℕ) :
    (cutProj (A := A) c) n = if c ≤ n then 1 else 0 := rfl

theorem cutProj_mul_self (c : ℕ) :
    cutProj (A := A) c * cutProj c = cutProj c := by
  refine lp.ext (funext fun n ↦ ?_)
  rw [lp.infty_coeFn_mul]
  by_cases h : c ≤ n <;> simp [h]

theorem star_cutProj (c : ℕ) : star (cutProj (A := A) c) = cutProj c := by
  refine lp.ext (funext fun n ↦ ?_)
  by_cases h : c ≤ n <;> simp [h]

theorem cutProj_comm (c : ℕ) (x : StarStrong.BoundedStarSequence A) :
    cutProj (A := A) c * x = x * cutProj c := by
  refine lp.ext (funext fun n ↦ ?_)
  rw [lp.infty_coeFn_mul, lp.infty_coeFn_mul]
  by_cases h : c ≤ n <;> simp [h]

/-- **Truncation past a cut**, as a non-unital `*`-homomorphism of the bounded
product: multiplication by a central self-adjoint idempotent. -/
def truncSeq (c : ℕ) : StarStrong.BoundedStarSequence A →⋆ₙₐ[ℂ]
    StarStrong.BoundedStarSequence A where
  toFun x := cutProj c * x
  map_zero' := mul_zero _
  map_add' x y := mul_add _ _ _
  map_smul' z x := mul_smul_comm z (cutProj c) x
  map_mul' x y := by
    refine lp.ext (funext fun n ↦ ?_)
    rw [lp.infty_coeFn_mul, lp.infty_coeFn_mul, lp.infty_coeFn_mul,
      lp.infty_coeFn_mul]
    by_cases h : c ≤ n <;> simp [h]
  map_star' x := by
    rw [star_mul, star_cutProj, ← cutProj_comm]

@[simp] theorem truncSeq_apply (c : ℕ) (x : StarStrong.BoundedStarSequence A) :
    truncSeq (A := A) c x = cutProj c * x := rfl

theorem truncSeq_coord (c : ℕ) (x : StarStrong.BoundedStarSequence A) (n : ℕ) :
    (truncSeq (A := A) c x) n = if c ≤ n then x n else 0 := by
  rw [truncSeq_apply, lp.infty_coeFn_mul]
  by_cases h : c ≤ n <;> simp [h]

/-- Truncation is contractive at every coordinate. -/
theorem norm_truncSeq_coord_le (c : ℕ) (x : StarStrong.BoundedStarSequence A)
    (n : ℕ) : ‖(truncSeq (A := A) c x) n‖ ≤ ‖x n‖ := by
  rw [truncSeq_coord]
  by_cases h : c ≤ n
  · rw [if_pos h]
  · rw [if_neg h, norm_zero]
    exact norm_nonneg _

/-- **The bridge.**  A family controlled past its cut becomes controlled in the
norm of `𝒟` once it is truncated there, because truncation zeroes exactly the
coordinates the tail condition says nothing about. -/
theorem tendsto_norm_truncSeq_of_tailNull {cut : ℕ → ℕ}
    {X : ℕ → StarStrong.BoundedStarSequence A} (h : TailNull cut X) :
    Tendsto (fun t ↦ ‖truncSeq (A := A) (cut t) (X t)‖) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨T, hT⟩ := eventually_atTop.mp (h (ε / 2) (by linarith))
  refine ⟨T, fun t ht ↦ ?_⟩
  have hbound : ‖truncSeq (A := A) (cut t) (X t)‖ ≤ ε / 2 := by
    refine lp.norm_le_of_forall_le (by linarith) fun n ↦ ?_
    rw [truncSeq_coord]
    by_cases hn : cut t ≤ n
    · rw [if_pos hn]
      exact hT t ht n hn
    · rw [if_neg hn, norm_zero]
      linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

/-- **What truncation costs.**  The unit is not preserved: the truncated unit is
the projection, which is at distance one from the unit whenever the cut is
positive.  This is why a glued map built from a tail lift is unital into a
corner and not into the whole reduced product. -/
theorem truncSeq_one (c : ℕ) :
    truncSeq (A := A) c 1 = cutProj c := by
  rw [truncSeq_apply, mul_one]

end Truncation

end

end ShulmanFill
end GroupApproximation
