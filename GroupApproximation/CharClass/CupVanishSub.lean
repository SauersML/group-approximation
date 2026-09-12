import GroupApproximation.CharClass.CupVanishCover
import GroupApproximation.CharClass.LerayHirschRel

/-!
# The two-set theorem over an ambient open set

The two-set theorem is stated for a cover of the whole space, which is what its
proof needs, but an induction over a finite cover meets it one union at a time.
This file supplies that form: for opens `A` and `B`, classes vanishing on each
have a product vanishing on `A ⊔ B`.

There is nothing new in the proof.  Inside their union two opens cover, which is
`opRel_sup_eq_top`, and an open inside a larger open is itself, which is
`relIso`; the composite of the two inclusions is the one inclusion, and that
identity is definitional.  So the whole content is transporting the hypotheses
along `relIso` and applying the theorem on the subspace.

## Main declarations

* `pull_cup_eq_zero_of_sup` — **the two-set theorem over `A ⊔ B`.**
-/

set_option autoImplicit false

namespace GroupApproximation.CharClass

open CategoryTheory TopologicalSpace
open GroupApproximation.CharClass.LH

noncomputable section

variable {X : TopCat.{0}}

/-- **The two-set theorem over an ambient open set.**  If `a` vanishes on `A` and
`b` vanishes on `B`, then `a ⌣ b` vanishes on `A ⊔ B`. -/
theorem pull_cup_eq_zero_of_sup (A B : Opens X) {p q : ℕ} (hpq : 0 < p + q)
    (a : Hmod2 X p) (b : Hmod2 X q)
    (ha : pull (opIncl A) p a = 0) (hb : pull (opIncl B) q b = 0) :
    pull (opIncl (A ⊔ B)) (p + q) (cup a b) = 0 := by
  have hA : A ≤ A ⊔ B := le_sup_left
  have hB : B ≤ A ⊔ B := le_sup_right
  rw [pull_cup]
  refine cup_eq_zero_of_absToSub_eq_zero (opRel A (A ⊔ B)) (opRel B (A ⊔ B))
    (opRel_sup_eq_top A B) hpq _ _ ?_ ?_
  · show pull (opIncl (opRel A (A ⊔ B))) p (pull (opIncl (A ⊔ B)) p a) = 0
    rw [← pull_comp, ← relIso_hom_comp_opIncl A (A ⊔ B) hA, pull_comp, ha, pull_zero]
  · show pull (opIncl (opRel B (A ⊔ B))) q (pull (opIncl (A ⊔ B)) q b) = 0
    rw [← pull_comp, ← relIso_hom_comp_opIncl B (A ⊔ B) hB, pull_comp, hb, pull_zero]

end

end GroupApproximation.CharClass
