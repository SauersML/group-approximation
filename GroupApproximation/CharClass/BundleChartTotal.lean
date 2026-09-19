import GroupApproximation.CharClass.BundleGysinPieces

/-!
# Complex vector bundles in the projection model, XXIX: the chart open is the
total space

`chartOpensHomotopyEquivBase` is assembled over a homeomorphism that was never
named: the chart open of `P(p ⊕ 1)`, viewed inside the projective bundle, **is**
the total space `E(p)`.  A Thom bridge needs that homeomorphism itself, not the
homotopy equivalence built on it, together with the two facts that make it a map
of pairs: the zero section corresponds to the zero section, and the part of the
chart off the zero section corresponds to `E(p) ∖ 0`.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open scoped Matrix
open GroupApproximation.STW59

namespace Bundle

section ChartTotal

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The chart open of `P(p ⊕ 1)` is the total space of `p`.** -/
noncomputable def chartOpensHomeoTotal (p : Bundle X ι) :
    ↥(chartOpensSet p) ≃ₜ Total p :=
  (chartHomeoOpens p).symm.trans (totalHomeoChart p).symm

omit [DecidableEq ι] in
theorem zeroSectionProj_mem_chartOpensSet (p : Bundle X ι) (x : X) :
    zeroSectionProj p x ∈ chartOpensSet p := by
  show betaEntry ((x, infPoint ι) : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ≠ 0
  have h : betaEntry ((x, infPoint ι) : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) = 1 := by
    show rankOneProj (Sum.elim (0 : ι → ℂ) (fun _ : Unit => (1 : ℂ)))
        (Sum.inr ()) (Sum.inr ()) = 1
    rw [rankOneProj_apply]
    simp
  rw [h]
  exact one_ne_zero

omit [DecidableEq ι] in
/-- **The zero section corresponds to the zero section.** -/
theorem chartOpensHomeoTotal_zeroSectionProj (p : Bundle X ι) (x : X) :
    chartOpensHomeoTotal p ⟨zeroSectionProj p x, zeroSectionProj_mem_chartOpensSet p x⟩
      = zeroSection p x := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  funext i
  show rankOneProj (Sum.elim (0 : ι → ℂ) (fun _ : Unit => (1 : ℂ))) (Sum.inl i) (Sum.inr ())
      / betaEntry ((x, infPoint ι) : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) = 0
  rw [rankOneProj_apply]
  simp

/-- **It is a map of pairs.**  A point of the chart lies off the zero section
exactly when its total-space image does. -/
theorem chartOpensHomeoTotal_mem_puncturedSet (p : Bundle X ι) (z : ↥(chartOpensSet p)) :
    ((chartOpensHomeoTotal p z : Total p) : X × (ι → ℂ)) ∈ puncturedSet p
      ↔ (z : Proj p.plusOne) ∈ notZeroOpensSet p := by
  set c : Chart p := (chartHomeoOpens p).symm z with hc
  have hv : chartOpensHomeoTotal p z = totalOf p c := rfl
  constructor
  · intro h
    have h2 := (chartOf_mem_notZeroSet_iff p (totalOf p c)).mpr (by
      rw [← hv]; exact h.2)
    rw [chartOf_totalOf] at h2
    exact h2.2
  · intro h
    refine ⟨(totalOf p c).2, ?_⟩
    have h2 : (chartOf p (totalOf p c) : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ)
        ∈ notZeroSet p := by
      rw [chartOf_totalOf]
      exact ⟨(z : Proj p.plusOne).2, h⟩
    have h3 := (chartOf_mem_notZeroSet_iff p (totalOf p c)).mp h2
    rw [hv]
    exact h3

end ChartTotal

end Bundle

end CharClass
end GroupApproximation
