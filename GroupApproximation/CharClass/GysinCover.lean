import GroupApproximation.CharClass.BundleZeroSection
import GroupApproximation.CharClass.CohomologyBasic

/-!
# The Mayer–Vietoris cover behind the Gysin sequence

The Gysin sequence of the circle bundle of `p` comes from the two-open cover

```text
P(p ⊕ 1)  =  E(p)  ∪  (P(p ⊕ 1) ∖ Z),
```

the affine chart and the complement of the zero section, whose intersection is
`E(p) ∖ 0` and so retracts onto the sphere bundle.  `cc-bundle` supplies both
opens and the retractions; what is missing, and is proved here, is that they
**cover**.

That is a one-line identity in the projection model.  A point of `P(p ⊕ 1)` is
the line spanned by a unit vector `w` of `ℂ^ι ⊕ ℂ`; the chart is cut out by the
`Unit`-block entry `β = ‖w(∗)‖²`, and the complement of the zero section by the
`ι`-block trace `‖w ∘ inl‖²`.  Those two add up to `‖w‖² = 1`, so they cannot both
vanish.  No choice of a spanning vector survives into the statement, since both
functions are continuous on the total space.

## Main declarations

* `Gysin.betaEntry_ne_zero_or_zTrace_ne_zero` — the covering identity.
* `Gysin.chartOpens`, `Gysin.notZeroOpens` — the two pieces as `Opens`.
* `Gysin.chartOpens_sup_notZeroOpens` — they cover, in the form the element-level
  Mayer–Vietoris sequence consumes.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59

namespace Gysin

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The chart and the complement of the zero section cover `P(p ⊕ 1)`.**

For a point spanned by a unit vector `w`, the `Unit`-block entry is `‖w(∗)‖²` and
the `ι`-block trace is `‖w ∘ inl‖²`; they sum to `‖w‖² = 1`. -/
theorem betaEntry_ne_zero_or_zTrace_ne_zero (p : Bundle X ι)
    {z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ} (hz : z ∈ Bundle.projSet p.plusOne) :
    Bundle.betaEntry z ≠ 0 ∨ Bundle.zTrace z ≠ 0 := by
  obtain ⟨w, hw, hzw, -⟩ := Bundle.exists_unitVector_of_mem_projSet hz
  have hpair : z = ((z.1, rankOneProj w) : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) :=
    Prod.ext rfl hzw
  -- the two block quantities, as real numbers
  have hbeta : Bundle.betaEntry z = ((‖w (Sum.inr ())‖ ^ 2 : ℝ) : ℂ) := by
    rw [Bundle.betaEntry_def, hzw, rankOneProj_apply]
    exact mul_star_self_eq_normSq _
  have htr : Bundle.zTrace z = ((eucNormSq (w ∘ Sum.inl) : ℝ) : ℂ) := by
    rw [hpair]
    exact Bundle.zTrace_of_rankOneProj z.1 w
  -- they sum to one
  have hinr : eucNormSq (w ∘ Sum.inr) = ‖w (Sum.inr ())‖ ^ 2 := by
    rw [eucNormSq_def]
    simp
  have hsum : eucNormSq (w ∘ Sum.inl) + ‖w (Sum.inr ())‖ ^ 2 = 1 := by
    rw [← hinr, ← Bundle.eucNormSq_sum_type]
    exact mem_unitVectors_iff_eucNormSq.mp hw
  by_contra hcon
  simp only [not_or, not_not] at hcon
  obtain ⟨hb, ht⟩ := hcon
  rw [hbeta] at hb
  rw [htr] at ht
  have hb' : ‖w (Sum.inr ())‖ ^ 2 = 0 := by exact_mod_cast hb
  have ht' : eucNormSq (w ∘ Sum.inl) = 0 := by exact_mod_cast ht
  rw [hb', ht', add_zero] at hsum
  exact zero_ne_one hsum

/-- The affine chart `E(p)`, as an open of `P(p ⊕ 1)`. -/
def chartOpens (p : Bundle X ι) : Opens (TopCat.of (Bundle.Proj p.plusOne)) :=
  ⟨{z : Bundle.Proj p.plusOne |
      Bundle.betaEntry (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ≠ 0},
    Bundle.isOpen_chart_in_proj p⟩

/-- The complement of the zero section, as an open of `P(p ⊕ 1)`. -/
def notZeroOpens (p : Bundle X ι) : Opens (TopCat.of (Bundle.Proj p.plusOne)) :=
  ⟨{z : Bundle.Proj p.plusOne |
      Bundle.zTrace (z : X × Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℂ) ≠ 0},
    Bundle.isOpen_notZero_in_proj p⟩

/-- **The Gysin cover.** -/
theorem chartOpens_sup_notZeroOpens (p : Bundle X ι) :
    chartOpens p ⊔ notZeroOpens p = ⊤ := by
  refine Opens.ext ?_
  rw [Opens.coe_sup, Opens.coe_top]
  refine Set.eq_univ_of_forall fun z => ?_
  exact betaEntry_ne_zero_or_zTrace_ne_zero p z.2

end

end Gysin

end CharClass
end GroupApproximation
