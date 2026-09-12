import GroupApproximation.CharClass.LIXProductChart
import GroupApproximation.CharClass.LemmaTwoTopClass

/-!
# The chart at the local model's own coordinates

Lane `cc-lix-odd`.

`LIXProductChart` gives the chart onto `(ℂ³) × ∏ⱼ ℂ^{dⱼ}`.  `cc-thom`'s local model is
`Fin r → ℂ` with `r = lixRank dd`.  Those have the same real dimension,
`6 + 2 ∑ⱼ dⱼ = 2 r`, so the passage between them is a linear homeomorphism and not
mathematics.

**It is done by a dimension count, deliberately.**  The index route needs a currying
homeomorphism, a sum-to-product homeomorphism and a reindexing along an equivalence of
finite types, each with its own coherence obligations.  `ContinuousLinearEquiv.ofFinrankEq`
replaces all three with one arithmetic identity, which is the whole content.

## Main results

* `lixCoordEquiv` — the coordinate change, from a dimension count.
* `lixFullChart` — **the chart at the full rank, into `Fin r → ℂ`**, with the zero in its
  source, the origin in its target, and its value at the zero pinned.
-/

noncomputable section

namespace GroupApproximation.CharClass

open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The coordinate change -/

theorem finrank_lixProductTarget (dd : Fin ℓ → ℕ) :
    Module.finrank ℝ ((Fin 3 → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      = Module.finrank ℝ (Fin (lixRank dd) → ℂ) := by
  have hL : Module.finrank ℝ ((Fin 3 → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      = 6 + ∑ x, dd x * 2 := by
    simp [Module.finrank_prod, Module.finrank_pi_fintype, Complex.finrank_real_complex]
  have hR : Module.finrank ℝ (Fin (lixRank dd) → ℂ) = lixRank dd * 2 := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  rw [hL, hR, lixRank, ← Finset.sum_mul]
  ring

/-- **The coordinate change**, from the dimension count alone. -/
def lixCoordEquiv (dd : Fin ℓ → ℕ) :
    ((Fin 3 → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ≃L[ℝ] (Fin (lixRank dd) → ℂ) :=
  ContinuousLinearEquiv.ofFinrankEq (finrank_lixProductTarget dd)

/-! ## 2. The chart at the full rank -/

/-- **The chart of the section at its zero, in the local model's coordinates.** -/
def lixFullChart (dd : Fin ℓ → ℕ) :
    OpenPartialHomeomorph (ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      (Fin (lixRank dd) → ℂ) :=
  (lixProductChart dd).transHomeomorph (lixCoordEquiv dd).toHomeomorph

theorem zero_mem_lixFullChart_source :
    ((0, 0) : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ∈ (lixFullChart dd).source :=
  zero_mem_lixProductChart_source

theorem lixFullChart_zero :
    lixFullChart dd ((0, 0) : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      = (0 : Fin (lixRank dd) → ℂ) := by
  show (lixCoordEquiv dd) (lixProductChart dd (0, 0)) = 0
  rw [lixProductChart_zero]
  exact map_zero _

theorem zero_mem_lixFullChart_target :
    (0 : Fin (lixRank dd) → ℂ) ∈ (lixFullChart dd).target := by
  have h : lixFullChart dd ((0, 0) : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      ∈ (lixFullChart dd).target :=
    (lixFullChart dd).map_source zero_mem_lixFullChart_source
  rwa [lixFullChart_zero] at h

end GroupApproximation.CharClass
