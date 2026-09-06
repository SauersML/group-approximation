import GroupApproximation.CharClass.LIXChartIso

/-!
# A convex neighbourhood of the section's zero

Lane `cc-lix-odd`.

`cc-relative`'s identification of a product pair with the local model takes the base
**contractible**.  `cc-bundle`'s trivialising set is not contractible in general, and
neither is the source of a chart produced by the inverse function theorem.  Both are open
and both contain the origin, so a metric ball inside their intersection serves: balls in a
normed space are convex, and a nonempty convex set is contractible.

The chart source lives in `ChartSrc × ∏ⱼ ℂ^{dⱼ}`, a real normed space, so the ball is
available with no construction.

## Main results

* `lixEps`, `lixBall` — the radius and the ball, with `lixEps_pos` and `isOpen_lixBall`.
* `lixBall_subset_source`, `zero_mem_lixBall`.
* `contractibleSpace_lixBall` — **the hypothesis `cc-relative`'s corollary wants**.
-/

noncomputable section

namespace GroupApproximation.CharClass

open Set Metric
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. A ball inside the common chart source -/

theorem exists_ball_subset_lixBC_source (dd : Fin ℓ → ℕ) :
    ∃ ε > 0, ball (0 : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ε ⊆ (lixBC dd).source :=
  Metric.isOpen_iff.mp (lixBC dd).open_source _ zero_mem_lixBC_source

/-- A radius whose ball lies inside the common chart source. -/
def lixEps (dd : Fin ℓ → ℕ) : ℝ := (exists_ball_subset_lixBC_source dd).choose

theorem lixEps_pos : 0 < lixEps dd :=
  (exists_ball_subset_lixBC_source dd).choose_spec.1

/-- **The convex neighbourhood of the section's zero.** -/
def lixBall (dd : Fin ℓ → ℕ) : Set (ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) :=
  ball 0 (lixEps dd)

theorem lixBall_subset_source : lixBall dd ⊆ (lixBC dd).source :=
  (exists_ball_subset_lixBC_source dd).choose_spec.2

theorem isOpen_lixBall : IsOpen (lixBall dd) := isOpen_ball

theorem zero_mem_lixBall :
    ((0, 0) : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ∈ lixBall dd :=
  mem_ball_self lixEps_pos

/-! ## 2. It is contractible -/

theorem convex_lixBall : Convex ℝ (lixBall dd) := convex_ball _ _

/-- **The contractibility `cc-relative`'s corollary takes as its hypothesis.** -/
theorem contractibleSpace_lixBall : ContractibleSpace ↥(lixBall dd) :=
  (convex_lixBall (dd := dd)).contractibleSpace ⟨_, zero_mem_lixBall⟩

end GroupApproximation.CharClass
