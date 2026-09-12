import GroupApproximation.CharClass.LIXVDecomposition
import GroupApproximation.CharClass.BundleBasic

/-!
# `V` as a bundle over the projective base, with its rank

Lane `cc-lix-odd`, for `cc-steenrod`'s split relation.

`splitRelation_of_sum` wants the rank as `Bundle.rank`, not as a trace, and it wants the
bundle over the base its slice lives on.

**`V` does not depend on the five-sphere factor.**  `Hmat` reads only `m.2`, so `Vmat`
factors through `baseY dd`, and the bundle belongs there rather than over `baseM dd`.  That
is also the base `cc-steenrod`'s slice class and `cc-wu`'s transport are stated over, so no
projection or pullback is needed anywhere.

## Main results

* `VmatY` — `V` as a function of the projective coordinates alone, with `VmatY_eq`.
* `vBundleY` — the bundle.
* `rank_vBundleY` — **`∀ y, rank y = (∑ⱼ dⱼ) + 3`**, in the form the split relation takes.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. `V` over the projective base -/

/-- The `H` block, as a function of the projective coordinates alone. -/
def HmatY (y : baseY dd) : Matrix (HIdx dd) (HIdx dd) ℂ :=
  Matrix.blockDiagonal' fun b : HBlk dd =>
    ((y b.1 : CP (dd b.1)) : Matrix (Fin (dd b.1 + 1)) (Fin (dd b.1 + 1)) ℂ)

/-- `V = 𝟏³ ⊕ H`, over the projective base. -/
def VmatY (y : baseY dd) : Matrix (VIdx dd) (VIdx dd) ℂ :=
  Matrix.fromBlocks 1 0 0 (HmatY y)

/-- `V` really does not see the five-sphere factor. -/
theorem VmatY_eq (m : baseM dd) : VmatY m.2 = Vmat m := rfl

/-! ## 2. The bundle -/

theorem continuous_VmatY : Continuous (VmatY (dd := dd)) := by
  have h : Continuous fun y : baseY dd => Vmat ((negEThree, y) : baseM dd) :=
    continuous_Vmat.comp (continuous_const.prodMk continuous_id)
  exact h

theorem isStarProjection_VmatY (y : baseY dd) : IsStarProjection (VmatY y) :=
  isStarProjection_Vmat ((negEThree, y) : baseM dd)

/-- **`V` as a bundle over the projective base.** -/
def vBundleY (dd : Fin ℓ → ℕ) : Bundle (baseY dd) (VIdx dd) where
  toFun := VmatY
  continuous_toFun := continuous_VmatY
  isStarProjection_toFun := isStarProjection_VmatY

@[simp] theorem coe_vBundleY : ⇑(vBundleY dd) = VmatY (dd := dd) := rfl

/-! ## 3. The rank -/

theorem trace_VmatY (y : baseY dd) :
    Matrix.trace (VmatY y) = (((∑ j, dd j : ℕ) + 3 : ℕ) : ℂ) :=
  trace_Vmat ((negEThree, y) : baseM dd)

/-- **The rank, in the form `splitRelation_of_sum` consumes.**  `Bundle.rank`, not the
trace; the two are different hypotheses in this model. -/
theorem rank_vBundleY (dd : Fin ℓ → ℕ) (y : baseY dd) :
    (vBundleY dd).rank y = (∑ j, dd j) + 3 := by
  have htr : Matrix.trace ((vBundleY dd) y) = ((((∑ j, dd j) + 3 : ℕ) : ℕ) : ℂ) := by
    show Matrix.trace (VmatY y) = _
    exact trace_VmatY y
  have h := Bundle.trace_eq_rank (vBundleY dd) y
  rw [htr] at h
  exact_mod_cast h.symm

/-! The lane's `lixRank` abbreviation is deliberately not used here: it lives in
`LemmaTwoTopClass`, which this file does not import, and referring to it would silently
become an `autoImplicit` variable rather than an error.  The explicit sum is also the form
`splitRelation_of_sum` consumes. -/

end GroupApproximation.CharClass
