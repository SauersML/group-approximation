import GroupApproximation.CharClass.ProjectiveSpaceChart
import GroupApproximation.AlgTop.CPTautologicalSection

/-!
# The H-block section in the affine chart

Lane `cc-lix-odd` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`CharClass/LIXSectionLocalHomeo.lean` charts the section's **trivial block**, six real
dimensions onto `ℂ³`.  The base has real dimension `2(∑ⱼ dⱼ) + 6`, so for a nonempty tower
that is not the whole of it: the section's zero condition has four conjuncts and the chart
covers three, the fourth being that the projective coordinates sit at their base points.

This file computes the missing block in `cc-projective`'s affine chart, which is the first
step of the product chart at the full rank.

## The formula, and the one thing it shows

With `chartAt w = [1 : w₁ : ⋯ : w_d]`,

```text
tautColSection (chartAt w) i j = chartVec w j * conj (wᵢ) / (1 + ∑ₖ ‖wₖ‖²),
```

so the component at `j = 0` is `conj (wᵢ) / (1 + ∑ₖ ‖wₖ‖²)`.

**The leading behaviour at the base point is complex conjugation**, not the identity. That
is harmless here and worth recording: conjugation is an `ℝ`-linear isomorphism, so the
section is still a local homeomorphism at the zero, and the mod-2 argument needs only a
homeomorphism of pairs, never a degree or an orientation. A route that wanted a
holomorphic chart or a complex-linear derivative would fail exactly here.

## A vocabulary note

`entry` exists twice, as `AlgTop.CPn.entry` and `CharClass.CPn.entry`, with identical
bodies over the same `CP d`. Both are `abbrev`, so they interchange definitionally and the
chart lemmas of one namespace apply to the section of the other; that is why the proof
below is a `simpa` and not a transport.

## Main results

* `tautColSection_chartAt` — the section in the chart, all components.
* `tautColSection_chartAt_zero` — the `j = 0` component, where the conjugation is visible.
* `tautColSection_chartAt_eq_zero_iff` — in the chart, the section vanishes only at `0`.
-/

noncomputable section

namespace GroupApproximation.CharClass

open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-- **The tautological column section, in the affine chart.** -/
theorem tautColSection_chartAt (w : Fin d → ℂ) (i : Fin d) (j : Fin (d + 1)) :
    AlgTop.CPn.tautColSection (CPn.chartAt w) i j
      = CPn.chartVec w j * star (w i) / ((CPn.sqNorm (CPn.chartVec w) : ℝ) : ℂ) := by
  have h := CPn.chartAt_entry w j i.succ
  rw [CPn.chartVec_succ] at h
  simpa using h

/-- **The component where the conjugation is visible.**  At `j = 0` the section is
`conj (wᵢ)` divided by a positive real, so its leading part at `w = 0` is conjugation. -/
theorem tautColSection_chartAt_zero (w : Fin d → ℂ) (i : Fin d) :
    AlgTop.CPn.tautColSection (CPn.chartAt w) i 0
      = star (w i) / ((1 + ∑ k, ‖w k‖ ^ 2 : ℝ) : ℂ) := by
  rw [tautColSection_chartAt, CPn.chartVec_zero, one_mul, CPn.chartVec_sqNorm]

/-- **In the chart the section vanishes exactly at the origin.**  The transport of
`tautColSection_eq_zero_iff` through `chartAt_zero`, in the coordinates the product chart
will use. -/
theorem tautColSection_chartAt_eq_zero_iff (w : Fin d → ℂ) :
    AlgTop.CPn.tautColSection (CPn.chartAt w) = 0 ↔ w = 0 := by
  constructor
  · intro h
    funext i
    have h0 := congrFun (congrFun h i) 0
    rw [tautColSection_chartAt_zero] at h0
    have hden : ((1 + ∑ k, ‖w k‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have hpos : (0 : ℝ) < 1 + ∑ k, ‖w k‖ ^ 2 := by
        have : (0:ℝ) ≤ ∑ k, ‖w k‖ ^ 2 := Finset.sum_nonneg fun k _ => by positivity
        linarith
      exact_mod_cast hpos.ne'
    have hstar : star (w i) = 0 := by
      field_simp at h0
      simpa using h0
    simpa using congrArg star hstar
  · intro h
    subst h
    funext i j
    rw [tautColSection_chartAt]
    simp

end GroupApproximation.CharClass
