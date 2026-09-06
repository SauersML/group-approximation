import GroupApproximation.CharClass.LIXBallNeighbourhood

/-!
# A contractible neighbourhood of the zero, inside any prescribed open set

Lane `cc-lix-odd`.

`LIXBallNeighbourhood` gives a convex ball in *chart coordinates*.  The trivialising set of
`cc-bundle`'s frame lives in the *base*, so the ball has to be pushed forward, and it has
to be small enough to land inside whatever open set is prescribed.

This file does both at once, for an arbitrary open `U` containing the section's zero.
Instantiating `U` at a trivialising set is then a one-line application, whichever
trivialising set `cc-bundle`'s `totalTrivStdOn` ends up wanting.

## Main results

* `lixBaseBall` — the neighbourhood, as the chart image of a ball.
* `lixBaseBall_subset`, `lixZero_mem_lixBaseBall`, `isOpen_lixBaseBall`.
* `contractibleSpace_lixBaseBall` — **contractible**, which is what the product-pair
  identification consumes.
-/

noncomputable section

namespace GroupApproximation.CharClass

open Set Metric
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. A ball whose image lands in `U` -/

theorem exists_ball_image_subset (dd : Fin ℓ → ℕ)
    (U : Set (↥sphereOne × baseM dd)) (hU : IsOpen U) (hzU : lixZero dd ∈ U) :
    ∃ ε > 0, ball (0 : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ε ⊆
      (lixBC dd).source ∩ (lixBC dd) ⁻¹' U := by
  refine Metric.isOpen_iff.mp ?_ _ ⟨zero_mem_lixBC_source, ?_⟩
  · exact (lixBC dd).continuousOn.isOpen_inter_preimage (lixBC dd).open_source hU
  · show lixBC dd ((0, 0) : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ∈ U
    rw [lixBC_zero]
    exact hzU

/-- The radius of a ball whose chart image lies inside `U`. -/
def lixBaseEps (dd : Fin ℓ → ℕ) (U : Set (↥sphereOne × baseM dd)) (hU : IsOpen U)
    (hzU : lixZero dd ∈ U) : ℝ :=
  (exists_ball_image_subset dd U hU hzU).choose

theorem lixBaseEps_pos (U : Set (↥sphereOne × baseM dd)) (hU : IsOpen U)
    (hzU : lixZero dd ∈ U) : 0 < lixBaseEps dd U hU hzU :=
  (exists_ball_image_subset dd U hU hzU).choose_spec.1

theorem lixBaseBallPre_subset (U : Set (↥sphereOne × baseM dd)) (hU : IsOpen U)
    (hzU : lixZero dd ∈ U) :
    ball (0 : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) (lixBaseEps dd U hU hzU) ⊆
      (lixBC dd).source ∩ (lixBC dd) ⁻¹' U :=
  (exists_ball_image_subset dd U hU hzU).choose_spec.2

/-! ## 2. The neighbourhood in the base -/

/-- **A contractible open neighbourhood of the section's zero, inside `U`.** -/
def lixBaseBall (dd : Fin ℓ → ℕ) (U : Set (↥sphereOne × baseM dd)) (hU : IsOpen U)
    (hzU : lixZero dd ∈ U) : Set (↥sphereOne × baseM dd) :=
  (lixBC dd) '' ball 0 (lixBaseEps dd U hU hzU)

theorem lixBaseBall_subset (U : Set (↥sphereOne × baseM dd)) (hU : IsOpen U)
    (hzU : lixZero dd ∈ U) : lixBaseBall dd U hU hzU ⊆ U := by
  rintro _ ⟨w, hw, rfl⟩
  exact (lixBaseBallPre_subset U hU hzU hw).2

theorem isOpen_lixBaseBall (U : Set (↥sphereOne × baseM dd)) (hU : IsOpen U)
    (hzU : lixZero dd ∈ U) : IsOpen (lixBaseBall dd U hU hzU) :=
  ((lixBC dd).isOpen_image_iff_of_subset_source
    (fun _ hw => (lixBaseBallPre_subset U hU hzU hw).1)).mpr isOpen_ball

theorem lixZero_mem_lixBaseBall (U : Set (↥sphereOne × baseM dd)) (hU : IsOpen U)
    (hzU : lixZero dd ∈ U) : lixZero dd ∈ lixBaseBall dd U hU hzU :=
  ⟨(0, 0), mem_ball_self (lixBaseEps_pos U hU hzU), lixBC_zero⟩

/-! ## 3. Contractibility -/

/-- The chart, cut down to the ball: its source **is** the ball and its target **is** the
neighbourhood, so it is the homeomorphism that transports contractibility. -/
def lixBallChart (dd : Fin ℓ → ℕ) (U : Set (↥sphereOne × baseM dd)) (hU : IsOpen U)
    (hzU : lixZero dd ∈ U) :
    OpenPartialHomeomorph (ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
      (↥sphereOne × baseM dd) :=
  (lixBC dd).restrOpen (ball 0 (lixBaseEps dd U hU hzU)) isOpen_ball

theorem lixBallChart_source (U : Set (↥sphereOne × baseM dd)) (hU : IsOpen U)
    (hzU : lixZero dd ∈ U) :
    (lixBallChart dd U hU hzU).source
      = ball (0 : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) (lixBaseEps dd U hU hzU) := by
  rw [lixBallChart, OpenPartialHomeomorph.restrOpen_source]
  exact inter_eq_right.mpr fun _ hw => (lixBaseBallPre_subset U hU hzU hw).1

/-- **The neighbourhood is contractible**, being homeomorphic to a ball. -/
theorem contractibleSpace_lixBallChart_target (U : Set (↥sphereOne × baseM dd))
    (hU : IsOpen U) (hzU : lixZero dd ∈ U) :
    ContractibleSpace ↥(lixBallChart dd U hU hzU).target := by
  haveI : ContractibleSpace
      ↥(ball (0 : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) (lixBaseEps dd U hU hzU)) :=
    (convex_ball _ _).contractibleSpace ⟨_, mem_ball_self (lixBaseEps_pos U hU hzU)⟩
  haveI : ContractibleSpace ↥(lixBallChart dd U hU hzU).source :=
    (Homeomorph.setCongr (lixBallChart_source U hU hzU)).contractibleSpace
  exact (lixBallChart dd U hU hzU).toHomeomorphSourceTarget.symm.contractibleSpace

end GroupApproximation.CharClass
