import GroupApproximation.CharClass.ChernTotalRing
import GroupApproximation.CharClass.CohomologyDegreeZero

/-!
# The cohomology ring of a nonempty space is nontrivial

`ChernRelation` needs `Nontrivial (TotalH X)` at the base and at the flag space,
and nothing in the tree proves it.  It is the statement that `1 ≠ 0`, which in
this ring means `1 ≠ 0` in degree zero, which is
`one_ne_zero_cohZero` for a nonempty space.

The only content is that `1` in the ring is the degree-zero unit placed in its own
summand, so a class concentrated in one degree vanishes in the ring exactly when it
vanishes in that degree.  Both halves are already there:
`TotalH.of_one` is definitional and `TotalH.of_eq_zero_iff` is the concentration
lemma.

## Main declarations

* `nontrivial_totalH` — the theorem, from `Nonempty`.
* the instance form, so that instance search finds it through `TopCat.of`.
-/

namespace GroupApproximation.CharClass

noncomputable section

/-- **The mod-2 cohomology ring of a nonempty space is nontrivial.**  `1` sits in
degree zero, where it is the unit class, and that is nonzero as soon as the space
has a point. -/
theorem nontrivial_totalH (X : TopCat.{0}) [Nonempty X] : Nontrivial (TotalH X) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  rw [← TotalH.of_one X] at h
  exact one_ne_zero_cohZero X ((TotalH.of_eq_zero_iff X 0 (one X)).mp h)

/-- The instance form.  Stated at a general `TopCat` so that instance search
reaches it through `TopCat.of` as well. -/
instance nontrivial_totalH_inst (X : TopCat.{0}) [Nonempty X] :
    Nontrivial (TotalH X) :=
  nontrivial_totalH X

end

end GroupApproximation.CharClass
