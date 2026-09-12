import GroupApproximation.Analysis.VoiculescuMonotoneUnit

/-!
# (V1c) One step of the monotonisation

`Analysis/VoiculescuMonotoneUnit` states the datum the reduction needs — a
quasicentral approximate unit that is positive and *increasing* — and records why
the increasing half is not free: (V1b) builds its unit from convex averages of
late members, and averaging preserves positivity but destroys monotonicity.

The classical repair does not average.  It grows the unit by adding a piece
living in the complement of what is already there:

    `e' = e + (1-e)^{1/2} f (1-e)^{1/2}` .

This module is that step's algebra, and only its algebra.  Three identities carry
the whole construction:

* `le_improveUnit` — `e ≤ e'`, because the added term is a conjugate of a
  positive element and so positive.  This is the monotonicity, and it is the
  reason for the shape: nothing about `f` is needed beyond `0 ≤ f`.
* `improveUnit_le_one` — `e' ≤ 1`, because `f ≤ 1` conjugates to
  `(1-e)^{1/2} f (1-e)^{1/2} ≤ (1-e)`, so the step cannot overshoot.
* `one_sub_improveUnit` — `1 - e' = (1-e)^{1/2}(1-f)(1-e)^{1/2}`, which is how
  the *absorption* improves: the defect of `e'` is the defect of `e` conjugated
  by the defect of `f`.

## Stated abstractly

At a general C⋆-algebra, as everything order-and-calculus in this lane now is.
Written at `B(H)` the same statements drag the `PiLp`-style instance tower
through every `IsSelfAdjoint`, which has cost this lane several rounds; at an
abstract algebra the two paths to `Star` are the same variable.  The one
`B(H)`-specific fact — that the step preserves compactness — is transported at
the end, where it is an ideal argument and nothing else.

## What is not here

The quasicentrality of the step, which is where `(1-e)^{1/2}` has to almost
commute with the target family.  That is *not* a quantitative estimate: it is the
qualitative corona argument of
`Analysis/ShulmanCoronaSquareRootCommutator`, and it is the next module.
-/

namespace GroupApproximation
namespace ShulmanFill

noncomputable section

section Abstract

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonnegSpectrumClass ℝ A]

/-- **One step of Arveson's monotonisation.**  Grow `e` by a piece living in the
complement of what is already there. -/
def improveUnit (e f : A) : A := e + CFC.sqrt (1 - e) * f * CFC.sqrt (1 - e)

variable {e f : A}

theorem sqrt_one_sub_nonneg : 0 ≤ CFC.sqrt (1 - e) := CFC.sqrt_nonneg _

theorem sqrt_one_sub_mul_self (he1 : e ≤ 1) :
    CFC.sqrt (1 - e) * CFC.sqrt (1 - e) = 1 - e :=
  CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr he1)

/-- The added piece is positive; this is the whole of the monotonicity. -/
theorem conjugate_nonneg (hf0 : 0 ≤ f) :
    0 ≤ CFC.sqrt (1 - e) * f * CFC.sqrt (1 - e) :=
  conjugate_nonneg_of_nonneg hf0 sqrt_one_sub_nonneg

/-- **The step increases.** -/
theorem le_improveUnit (hf0 : 0 ≤ f) : e ≤ improveUnit e f :=
  le_add_of_nonneg_right (conjugate_nonneg hf0)

/-- **The step stays positive.** -/
theorem improveUnit_nonneg (he0 : 0 ≤ e) (hf0 : 0 ≤ f) : 0 ≤ improveUnit e f :=
  add_nonneg he0 (conjugate_nonneg hf0)

/-- **The step cannot overshoot.** -/
theorem improveUnit_le_one (he1 : e ≤ 1) (hf1 : f ≤ 1) : improveUnit e f ≤ 1 := by
  have hconj : CFC.sqrt (1 - e) * f * CFC.sqrt (1 - e) ≤ 1 - e := by
    refine le_trans (conjugate_le_conjugate_of_nonneg hf1 sqrt_one_sub_nonneg) ?_
    rw [mul_one, sqrt_one_sub_mul_self he1]
  have h : improveUnit e f ≤ e + (1 - e) := by
    rw [improveUnit]
    exact add_le_add (le_refl e) hconj
  simpa using h

/-- **The defect of the step is the defect of `e` conjugated by that of `f`.**
This is how the absorption improves, and it is the identity the recursion is
priced by. -/
theorem one_sub_improveUnit (he1 : e ≤ 1) :
    1 - improveUnit e f
      = CFC.sqrt (1 - e) * (1 - f) * CFC.sqrt (1 - e) := by
  rw [improveUnit, mul_sub, sub_mul, mul_one, sqrt_one_sub_mul_self he1]
  abel

/-- **The normalisation test.**  At `f = 1` the step completes in one move, so
the formula has the right coefficient: a step that added only part of the
complement would not reach `1` here. -/
theorem improveUnit_one (he1 : e ≤ 1) : improveUnit e (1 : A) = 1 := by
  rw [improveUnit, mul_one, sqrt_one_sub_mul_self he1]
  abel

/-- **The degenerate test.**  At `f = 0` the step does nothing, so the growth is
carried entirely by `f` and not by the conjugation. -/
theorem improveUnit_zero : improveUnit e (0 : A) = e := by
  rw [improveUnit, mul_zero, zero_mul, add_zero]

end Abstract

/-! ## The one fact that is not abstract -/

section Compact

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **The step preserves compactness**, because the compacts are an ideal: the
added piece is a compact conjugated by bounded operators. -/
theorem isCompactOperator_improveUnit {e f : H →L[ℂ] H}
    (he : IsCompactOperator e) (hf : IsCompactOperator f) :
    IsCompactOperator ((improveUnit e f : H →L[ℂ] H)) := by
  set c : H →L[ℂ] H := CFC.sqrt (1 - e) with hc
  have hleft : IsCompactOperator (⇑(f ∘L c)) := by
    have h := hf.comp_clm c
    rwa [← ContinuousLinearMap.coe_comp] at h
  have hboth : IsCompactOperator (⇑(c ∘L (f ∘L c))) := by
    have h := hleft.clm_comp c
    rwa [← ContinuousLinearMap.coe_comp] at h
  have hrw : improveUnit e f = e + c ∘L (f ∘L c) := by
    show e + c * f * c = e + c ∘L (f ∘L c)
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_assoc]
  rw [hrw]
  show IsCompactOperator ((⇑e : H → H) + ⇑(c ∘L (f ∘L c)))
  exact he.add hboth

end Compact

end

end ShulmanFill
end GroupApproximation
