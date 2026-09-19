import GroupApproximation.CharClass.LerayHirschDegree
import GroupApproximation.CharClass.ChernEulerSqOne
import GroupApproximation.CharClass.SqDataInstance

/-!
# The splitting data, over a Leray–Hirsch instance

`cc-wu`'s `SplittingData` has five fields, and three of them are consequences of
things this lane already has.  The projection and the roots are given; the
injectivity of the pullback on the ring is Leray–Hirsch plus `cc-wu`'s own bridge
from the degreewise statement; and the Steenrod field holds for any root that is
pulled back from a projective space, because the square lands in degree three
there.

So the whole obligation reduces to **Whitney on the flag bundle**, which is the
one genuinely remaining piece, and it is isolated here as a single hypothesis.

Written over the Leray–Hirsch instance as a named hypothesis, so that when the
instance lands these discharge in one line each.

## Main declarations

* `splittingDataOfGraded` — **the four discharged fields**, over Whitney.
* `hasSplitting_of_graded` — the same with the flag space hidden, which is the
  form a consumer takes.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

/-- **`cc-wu`'s splitting data, assembled.**  Everything but Whitney is
discharged: the pullback is injective on the ring because Leray–Hirsch makes it
injective in each degree, and `Sq¹` kills each root because a root is pulled back
from a projective space, whose degree three vanishes. -/
def splittingDataOfGraded {N F : TopCat.{0}} {r : ℕ} {γ : ℕ → TotalH N}
    (proj : F ⟶ N) (ξ : Hmod2 F 2) (rk : ℕ) (hrk : 0 < rk)
    (L : LerayHirschGraded proj ξ rk)
    (root : ℕ → Hmod2 F 2)
    (hroot : ∀ l : ℕ, ∃ (d : ℕ) (g : F ⟶ CPtop d) (h : Hmod2 (CPtop d) 2),
      root l = pull g 2 h)
    (hsplit : ∀ k : ℕ, TotalH.map proj (γ k)
      = esymmOn (Finset.range r) (fun l => TotalH.of F 2 (root l)) k) :
    Wu.SplittingData N F r γ where
  proj := proj
  root := root
  pull_injective := Wu.totalH_map_injective proj (fun n => L.pull_injective hrk n)
  sq_one_root := fun l => by
    obtain ⟨d, g, h, hg⟩ := hroot l
    rw [hg]
    exact CPn.sq_one_pull_eq_zero g h
  chern_split := hsplit

/-- The same with the flag space and the rank hidden, which is the form
`Wu.HasSplitting` and its consumers take. -/
theorem hasSplitting_of_graded {N F : TopCat.{0}} {r : ℕ} {γ : ℕ → TotalH N}
    (proj : F ⟶ N) (ξ : Hmod2 F 2) (rk : ℕ) (hrk : 0 < rk)
    (L : LerayHirschGraded proj ξ rk)
    (root : ℕ → Hmod2 F 2)
    (hroot : ∀ l : ℕ, ∃ (d : ℕ) (g : F ⟶ CPtop d) (h : Hmod2 (CPtop d) 2),
      root l = pull g 2 h)
    (hsplit : ∀ k : ℕ, TotalH.map proj (γ k)
      = esymmOn (Finset.range r) (fun l => TotalH.of F 2 (root l)) k) :
    Wu.HasSplitting N γ :=
  ⟨F, r, ⟨splittingDataOfGraded proj ξ rk hrk L root hroot hsplit⟩⟩

end

end LH
end CharClass
end GroupApproximation
