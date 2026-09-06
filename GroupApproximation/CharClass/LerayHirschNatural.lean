import GroupApproximation.CharClass.LerayHirschDegree
import GroupApproximation.CharClass.LerayHirschSquares
import GroupApproximation.CharClass.ProjectiveSpaceRing

/-!
# The Leray–Hirsch combination is natural in the base

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, items 3 and 4).

Everything this lane has proved about `lhMap` is at one base.  Restricting a class
to part of the base needs the other half: that the combination commutes with a
square

```text
P' --g--> P          g ≫ π = π' ≫ f ,   g^* ξ = ξ'
|π'       |π
X' --f--> X
```

`pull_lhMap` is that, and it is a two-line computation once the four pullback
identities are lined up.  The point of stating it is not difficulty but reach:
combined with injectivity of the combination downstairs it says the Leray–Hirsch
**coefficients** of a restricted class are the restrictions of the coefficients,
which is what a Thom class restricted to a trivialising neighbourhood needs.

## Main declarations

* `pull_lhMap` — **naturality of the combination.**
* `lhCoeff_natural` — hence the coefficients are natural, given injectivity
  downstairs.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable {X X' P P' : TopCat.{0}}

/-- **The Leray–Hirsch combination is natural.**  Over a square of spaces with the
degree-two class pulling back to the degree-two class, the combination of the
pulled-back coefficients is the pullback of the combination. -/
theorem pull_lhMap (f : X' ⟶ X) (g : P' ⟶ P) (π : P ⟶ X) (π' : P' ⟶ X')
    (hsq : g ≫ π = π' ≫ f) (ξ : Hmod2 P 2) (ξ' : Hmod2 P' 2)
    (hξ : pull g 2 ξ = ξ') (r n : ℕ)
    (a : (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ))) :
    pull g n (lhMap π ξ r n a)
      = lhMap π' ξ' r n (fun i => pull f (n - 2 * (i : ℕ)) (a i)) := by
  simp only [lhMap]
  rw [pull_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pull_cohCast, pull_cup, ← pull_comp, hsq, pull_comp, pull_cupPowE, hξ]

/-- **The coefficients are natural.**  If the combination downstairs is injective
-- which is one half of `LerayHirschGraded` there -- then the coefficients of a
restricted class are forced to be the restrictions of the coefficients.

Stated as a uniqueness principle rather than about a chosen coefficient family, so
that a consumer who already has a family in hand identifies it rather than
producing a second one. -/
theorem lhCoeff_natural (f : X' ⟶ X) (g : P' ⟶ P) (π : P ⟶ X) (π' : P' ⟶ X')
    (hsq : g ≫ π = π' ≫ f) (ξ : Hmod2 P 2) (ξ' : Hmod2 P' 2)
    (hξ : pull g 2 ξ = ξ') (r n : ℕ)
    (hinj : Function.Injective (lhMap π' ξ' r n))
    (a : (i : Fin (lhDomainCard r n)) → Hmod2 X (n - 2 * (i : ℕ)))
    (b : (i : Fin (lhDomainCard r n)) → Hmod2 X' (n - 2 * (i : ℕ)))
    (hb : lhMap π' ξ' r n b = pull g n (lhMap π ξ r n a)) :
    b = fun i : Fin (lhDomainCard r n) => pull f (n - 2 * (i : ℕ)) (a i) := by
  apply hinj
  rw [hb]
  exact pull_lhMap f g π π' hsq ξ ξ' hξ r n a

end

end LH
end CharClass
end GroupApproximation
