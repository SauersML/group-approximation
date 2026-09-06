import GroupApproximation.CharClass.LIXProjectiveBaseChart

/-!
# The projective factor as a partial homeomorphism, over the tower

Lane `cc-lix-odd`.

The affine chart is already a homeomorphism onto an open set, so the single-factor upgrade
is bookkeeping.  Over the tower the target is the product of the chart domains, which is
open because the index is finite.

## Main results

* `cpChartHomeo` — one projective factor, as an `OpenPartialHomeomorph`.
* `cpTowerChart` — **the whole tower**, with the origin at the base points.
-/

noncomputable section

namespace GroupApproximation.CharClass

open Set
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. One factor -/

theorem continuousOn_chartInv (d : ℕ) :
    ContinuousOn (CPn.chartInv (d := d)) (CPn.chartSet d) :=
  continuousOn_iff_continuous_restrict.mpr CPn.continuous_chartInv_on

/-- **One projective factor, as a partial homeomorphism.** -/
def cpChartHomeo (d : ℕ) : OpenPartialHomeomorph (Fin d → ℂ) (CP d) where
  toFun := CPn.chartAt
  invFun := CPn.chartInv
  source := univ
  target := CPn.chartSet d
  map_source' := fun w _ => CPn.chartAt_mem_chartSet w
  map_target' := fun _ _ => mem_univ _
  left_inv' := fun w _ => CPn.chartInv_chartAt w
  right_inv' := fun x hx => CPn.chartAt_chartInv x hx
  open_source := isOpen_univ
  open_target := CPn.isOpen_chartSet
  continuousOn_toFun := CPn.continuous_chartAt.continuousOn
  continuousOn_invFun := continuousOn_chartInv d

/-! ## 2. The tower -/

/-- The target of the tower chart: every coordinate in its own chart domain. -/
def cpTowerTarget (dd : Fin ℓ → ℕ) : Set (baseY dd) :=
  pi univ fun j => CPn.chartSet (dd j)

theorem isOpen_cpTowerTarget : IsOpen (cpTowerTarget dd) :=
  isOpen_set_pi finite_univ fun _ _ => CPn.isOpen_chartSet

theorem baseYPoint_mem_cpTowerTarget : baseYPoint dd ∈ cpTowerTarget dd := by
  intro j _
  show CPn.entry (baseYPoint dd j) 0 0 ≠ 0
  have : baseYPoint dd j = CPn.basePoint (dd j) := (basePoint_eq (dd j)).symm ▸ rfl
  rw [this, CPn.basePoint_entry]
  simp [CPn.baseVec]

/-- **The projective directions of the base chart, as a partial homeomorphism.** -/
def cpTowerChart (dd : Fin ℓ → ℕ) :
    OpenPartialHomeomorph (∀ j : Fin ℓ, Fin (dd j) → ℂ) (baseY dd) where
  toFun := cpBaseChartFun dd
  invFun := fun y j => CPn.chartInv (y j)
  source := univ
  target := cpTowerTarget dd
  map_source' := by
    intro z _ j _
    exact CPn.chartAt_mem_chartSet (z j)
  map_target' := fun _ _ => mem_univ _
  left_inv' := by
    intro z _
    funext j
    exact CPn.chartInv_chartAt (z j)
  right_inv' := by
    intro y hy
    funext j
    exact CPn.chartAt_chartInv (y j) (hy j (mem_univ j))
  open_source := isOpen_univ
  open_target := isOpen_cpTowerTarget
  continuousOn_toFun := continuous_cpBaseChartFun.continuousOn
  continuousOn_invFun := by
    refine continuousOn_pi.mpr fun j => ?_
    refine (continuousOn_chartInv (dd j)).comp (continuousOn_apply j _) ?_
    intro y hy
    exact hy j (mem_univ j)

end GroupApproximation.CharClass
