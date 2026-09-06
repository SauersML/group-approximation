import GroupApproximation.CharClass.ChernEulerBundle
import GroupApproximation.CharClass.SteenrodTotal
import GroupApproximation.CharClass.LerayHirschChart

/-!
# `Sq¹` kills the Euler class of a line bundle

`cc-wu`'s `SplittingData` asks that the first Steenrod square of each Chern root
vanish.  A root is the Euler class of a line bundle, hence a degree-two class
pulled back from a projective space, and `Sq¹` of it lands in degree three of that
projective space, which is zero because three is odd.

So the field is naturality of `Sq` composed with a vanishing that has been
available since the additive computation, and no Steenrod theory beyond
naturality enters.

## Main declarations

* `eq_zero_CP_three` — degree three of `ℂP^d` vanishes, in element form.
* `sq_one_pull_eq_zero` — `Sq¹` kills any degree-two class pulled back from `ℂP^d`.
* `sq_one_eulerClass`, `sq_one_eulerOfBundle` — **the `SplittingData` field**, for a
  root presented as an Euler class.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open CategoryTheory

noncomputable section

/-- Every class of `ℂP^d` in a degree that is not twice something at most `d`
vanishes.  Stated at an arbitrary degree so that a caller whose degree is written
as a sum never triggers a unification of that sum with a literal. -/
theorem eq_zero_CP_of_ne (d k : ℕ) (hk : ∀ n : ℕ, n ≤ d → k ≠ 2 * n)
    (a : Hmod2 (CPtop d) k) : a = 0 :=
  (hasCPCohomology_CP d).2 k hk a

/-- Degree three of `ℂP^d` vanishes: three is odd. -/
theorem eq_zero_CP_three (d : ℕ) (a : Hmod2 (CPtop d) 3) : a = 0 :=
  eq_zero_CP_of_ne d 3 (fun n _ => by omega) a

/-- **`Sq¹` kills a degree-two class pulled back from a projective space.**  The
square lands in degree three there, and that group is zero. -/
theorem sq_one_pull_eq_zero {F : TopCat.{0}} {d : ℕ} (g : F ⟶ CPtop d)
    (h : Hmod2 (CPtop d) 2) : Sq 1 (pull g 2 h) = 0 := by
  rw [Steenrod.Sq_pull g 1 2 h,
    eq_zero_CP_of_ne d (1 + 2) (fun n _ => by omega) (Sq 1 h), pull_zero]

/-- **`Sq¹` kills an Euler class.** -/
theorem sq_one_eulerClass {X : TopCat.{0}} {d : ℕ} (hgen : Hmod2 (CPtop d) 2)
    (f : X ⟶ CPtop d) : Sq 1 (eulerClass hgen f) = 0 :=
  sq_one_pull_eq_zero f hgen

/-- **`Sq¹` kills the Euler class of a line bundle**, which is `SplittingData`'s
`sq_one_root` for a root presented as an Euler class. -/
theorem sq_one_eulerOfBundle {X : Type} [TopologicalSpace X] {d : ℕ} (hd : 1 ≤ d)
    (p : Bundle X (Fin (d + 1))) (hp : ∀ x, (p x).trace = 1) :
    Sq 1 (eulerOfBundle hd p hp) = 0 :=
  sq_one_eulerClass (cpGen d hd) (cmap (Bundle.classifyOne p hp))

end

end CPn
end CharClass
end GroupApproximation
