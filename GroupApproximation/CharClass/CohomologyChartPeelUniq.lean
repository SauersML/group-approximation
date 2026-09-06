import GroupApproximation.CharClass.CohomologyChartLowDegree
import GroupApproximation.CharClass.CohomologyChartKunnethClosed

/-!
# One peel: what is determined, and what is not

`cpSplit_closed` peels a class on `U × ℂP^{d+1}` as a pullback from the base plus
the generator cupped with a class **on the total space**.  This file settles how
much of that data is unique.

The base coefficient is unique, unconditionally and at every rank.  Restricting
along the slice at a point of the fibre recovers it, and the slice composed with
the projection to the fibre is a constant map, which kills degree two.  No
Künneth statement is involved.

The other coefficient is **not** unique, and cannot be made so.  It is determined
only modulo the kernel of cupping with the generator, and that kernel is nonzero
as soon as the degree reaches twice the fibre dimension: the `r`-th power of the
generator, pulled back, is killed by one more generator because the `(r+1)`-st
power vanishes, while the `r`-th power itself does not.  Both halves of that are
`cc-projective`'s ring, `cupPowE_eq_zero_of_gt` and `cupPowE_cpGen_ne_zero`.

`cup_gen_eq_zero_of_peel_zero` records exactly what survives.  The rank-two case
looks different only because there the coefficient lives on the *base* and the
generator squares to zero, so the kernel has no room; the distinction is where
the coefficient lives, not the rank.

Anyone wanting freeness at general rank needs the full iterated decomposition,
with every coefficient pulled back from the base.  Iterating a one-step
uniqueness statement will not produce it, because there is no true one-step
uniqueness statement to iterate.

## Main declarations

* `KnCP.lhLow_gen` — the floor at the index `cpSplit_closed` is stated in.
* `KnCP.cpSliceGen_comp_cpPrCP` — the slice through the fibre is constant.
* `KnCP.peel_base_eq_zero` — **the base coefficient is unique**.  Note the degree
  is `2 + n`, not `n + 2`: that is the degree the cup product actually produces,
  and it is the one `cpSplit_closed` is stated in.
* `KnCP.cup_gen_eq_zero_of_peel_zero` — and the rest is exactly a kernel element.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-! ## 1. The floor, at the peeling index -/

/-- **The floor of the ladder at the index `cpSplit_closed` uses.**  This is
`lhLow_general` at `d + 1`; the two projections are the same morphism, since
`cpProdTop U d` is `U × ℂP^{d+1}`. -/
theorem lhLow_gen (n : ℕ) (hn : n < 2) : Function.Bijective (pull (cpPrU U d) n) :=
  lhLow_general U (d + 1) n hn

/-! ## 2. The slice through the fibre is constant -/

theorem cpSliceGen_comp_cpPrCP (p : CP (d + 1)) :
    cpSliceGen U (d + 1) p ≫ cpPrCP U d = cmap (ContinuousMap.const U p) := by
  apply TopCat.Hom.ext
  ext x
  rfl

/-! ## 3. The base coefficient is unique -/

set_option maxHeartbeats 1000000 in
/-- **The base coefficient of a peel is determined.**  If a peel vanishes then its
pullback part vanishes, at every rank and with no hypothesis on the base.  The
slice at a point of the fibre is a section of the projection, and it kills the
generator because it meets the fibre in a point. -/
theorem peel_base_eq_zero (hd : 1 ≤ d + 1) (n : ℕ)
    (a : Hmod2 (TopCat.of U) (2 + n)) (y : Hmod2 (cpProdTop U d) n)
    (h : pull (cpPrU U d) (2 + n) a
      + cup (pull (cpPrCP U d) 2 (cpGen (d + 1) hd)) y = 0) : a = 0 := by
  obtain ⟨p⟩ := nonempty_CPtop (d + 1)
  have hconst : pull (cpSliceGen U (d + 1) p ≫ cpPrCP U d) 2 (cpGen (d + 1) hd) = 0 := by
    rw [cpSliceGen_comp_cpPrCP]
    exact pull_const_eq_zero U p 2 (by omega) (cpGen (d + 1) hd)
  have hs := congrArg (pull (cpSliceGen U (d + 1) p) (2 + n)) h
  rw [pull_add, pull_zero, ← pull_comp, cpSliceGen_comp_cpFst, pull_id, pull_cup,
    ← pull_comp, hconst, zero_cup, add_zero] at hs
  exact hs

/-- **And the rest of a vanishing peel is exactly a kernel element.**  Together
with `peel_base_eq_zero` this is the whole truth of one-step uniqueness: the
second coefficient is constrained only to lie in the kernel of cupping with the
generator, and that kernel is not zero once the degree reaches twice the fibre
dimension. -/
theorem cup_gen_eq_zero_of_peel_zero (hd : 1 ≤ d + 1) (n : ℕ)
    (a : Hmod2 (TopCat.of U) (2 + n)) (y : Hmod2 (cpProdTop U d) n)
    (h : pull (cpPrU U d) (2 + n) a
      + cup (pull (cpPrCP U d) 2 (cpGen (d + 1) hd)) y = 0) :
    cup (pull (cpPrCP U d) 2 (cpGen (d + 1) hd)) y = 0 := by
  rw [peel_base_eq_zero U d hd n a y h, pull_zero, zero_add] at h
  exact h

end KnCP

end

end GroupApproximation.CharClass
