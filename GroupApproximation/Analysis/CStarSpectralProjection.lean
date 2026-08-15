import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# The spectral projection at an isolated top of the spectrum

For a self-adjoint element whose real spectrum meets `(c, ∞)` only in
`{1}`, the indicator of `(c, ∞)` is continuous on the spectrum and its
continuous functional calculus produces a self-adjoint idempotent `p`
absorbed by the element: `m * p = p * m = p`.

This is the projection brick of the strict-Kazhdan-compression program
of `docs/FORMALIZATION_DIRECTIVES_2026-08-15.md` §1: applied to the
unitary average of a Kazhdan set in the maximal group C-star algebra —
whose spectral gap is `AbstractSpectralGap.unitaryAverage_spectrum_le`
componentwise — it yields the Kazhdan projection.
-/

namespace GroupApproximation
namespace CStarSpectralProjection

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- The gap indicator: `1` strictly above the gap, `0` at or below it. -/
def gapIndicator (c : ℝ) : ℝ → ℝ := fun x => if c < x then 1 else 0

theorem gapIndicator_of_le {c x : ℝ} (h : x ≤ c) : gapIndicator c x = 0 :=
  if_neg (not_lt.mpr h)

theorem gapIndicator_of_lt {c x : ℝ} (h : c < x) : gapIndicator c x = 1 :=
  if_pos h

theorem gapIndicator_one {c : ℝ} (hc : c < 1) : gapIndicator c 1 = 1 :=
  gapIndicator_of_lt hc

/-- On a spectrum with a gap `(c, 1)` the indicator is continuous. -/
theorem continuousOn_gapIndicator {m : A} {c : ℝ} (hc : c < 1)
    (hgap : ∀ μ ∈ spectrum ℝ m, μ ≤ c ∨ μ = 1) :
    ContinuousOn (gapIndicator c) (spectrum ℝ m) := by
  intro x hx
  have hball : Metric.ball x (1 - c) ∩ spectrum ℝ m
      ∈ nhdsWithin x (spectrum ℝ m) :=
    inter_mem_nhdsWithin _ (Metric.ball_mem_nhds x (by linarith))
  rcases hgap x hx with hxc | hx1
  · have hev : gapIndicator c =ᶠ[nhdsWithin x (spectrum ℝ m)]
        fun _ => (0 : ℝ) := by
      refine Filter.eventuallyEq_of_mem hball ?_
      rintro y ⟨hyb, hys⟩
      rcases hgap y hys with hyc | hy1
      · exact gapIndicator_of_le hyc
      · exfalso
        rw [Metric.mem_ball, Real.dist_eq] at hyb
        rw [hy1] at hyb
        have habs : 1 - x < 1 - c := by
          calc 1 - x ≤ |1 - x| := le_abs_self _
            _ < 1 - c := hyb
        linarith
    exact (continuousWithinAt_const).congr_of_eventuallyEq hev
      (gapIndicator_of_le hxc)
  · subst hx1
    have hev : gapIndicator c =ᶠ[nhdsWithin x (spectrum ℝ m)]
        fun _ => (1 : ℝ) := by
      refine Filter.eventuallyEq_of_mem hball ?_
      rintro y ⟨hyb, hys⟩
      rcases hgap y hys with hyc | hy1
      · exfalso
        rw [Metric.mem_ball, Real.dist_eq] at hyb
        have habs : x - y < 1 - c := by
          calc x - y ≤ |y - x| := by
              rw [abs_sub_comm]
              exact le_abs_self _
            _ < 1 - c := hyb
        linarith
      · rw [hy1]
        exact gapIndicator_one hc
    exact (continuousWithinAt_const).congr_of_eventuallyEq hev
      (gapIndicator_one hc)

section Projection

variable (m : A) {c : ℝ}

/-- The spectral projection above the gap. -/
def spectralProjection (m : A) (c : ℝ) : A := cfc (gapIndicator c) m

theorem isSelfAdjoint_spectralProjection (hm : IsSelfAdjoint m) :
    IsSelfAdjoint (spectralProjection m c) :=
  cfc_predicate _ m

theorem isIdempotentElem_spectralProjection (hm : IsSelfAdjoint m)
    (hc : c < 1) (hgap : ∀ μ ∈ spectrum ℝ m, μ ≤ c ∨ μ = 1) :
    IsIdempotentElem (spectralProjection m c) := by
  have hcont := continuousOn_gapIndicator hc hgap
  rw [IsIdempotentElem, spectralProjection, ← cfc_mul _ _ m hcont hcont]
  apply cfc_congr
  intro x _
  by_cases hx : c < x
  · rw [gapIndicator_of_lt hx, mul_one]
  · rw [gapIndicator_of_le (not_lt.mp hx), mul_zero]

theorem mul_spectralProjection (hm : IsSelfAdjoint m) (hc : c < 1)
    (hgap : ∀ μ ∈ spectrum ℝ m, μ ≤ c ∨ μ = 1) :
    m * spectralProjection m c = spectralProjection m c := by
  have hcont := continuousOn_gapIndicator hc hgap
  have hid : m = cfc (fun x : ℝ => x) m := (cfc_id ℝ m).symm
  conv_lhs => rw [hid]
  rw [spectralProjection, ← cfc_mul _ _ m (continuousOn_id' _) hcont]
  apply cfc_congr
  intro x hx
  rcases hgap x hx with hxc | hx1
  · rw [gapIndicator_of_le hxc, mul_zero]
  · subst hx1
    rw [gapIndicator_one hc, mul_one]

theorem spectralProjection_mul (hm : IsSelfAdjoint m) (hc : c < 1)
    (hgap : ∀ μ ∈ spectrum ℝ m, μ ≤ c ∨ μ = 1) :
    spectralProjection m c * m = spectralProjection m c := by
  have hcont := continuousOn_gapIndicator hc hgap
  have hid : m = cfc (fun x : ℝ => x) m := (cfc_id ℝ m).symm
  conv_lhs => rw [hid]
  rw [spectralProjection, ← cfc_mul _ _ m hcont (continuousOn_id' _)]
  apply cfc_congr
  intro x hx
  rcases hgap x hx with hxc | hx1
  · rw [gapIndicator_of_le hxc, zero_mul]
  · subst hx1
    rw [gapIndicator_one hc, one_mul]

/-- The projection is nonzero exactly when `1` lies in the spectrum. -/
theorem spectralProjection_ne_zero (hm : IsSelfAdjoint m) (hc : c < 1)
    (hgap : ∀ μ ∈ spectrum ℝ m, μ ≤ c ∨ μ = 1)
    (h1 : (1 : ℝ) ∈ spectrum ℝ m) :
    spectralProjection m c ≠ 0 := by
  have hcont := continuousOn_gapIndicator hc hgap
  intro h0
  have hmap := cfc_map_spectrum (gapIndicator c) m (hf := hcont)
  rw [spectralProjection] at h0
  rw [h0] at hmap
  have hone : (1 : ℝ) ∈ spectrum ℝ (0 : A) := by
    rw [← hmap]
    exact ⟨1, h1, gapIndicator_one hc⟩
  rw [spectrum.zero_eq] at hone
  simp at hone

end Projection

end

end CStarSpectralProjection
end GroupApproximation
