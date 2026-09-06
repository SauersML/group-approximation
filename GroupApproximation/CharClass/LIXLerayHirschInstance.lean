import GroupApproximation.CharClass.LIXBaseInstances
import GroupApproximation.CharClass.LIXBundleModel
import GroupApproximation.CharClass.LerayHirschCompact

/-!
# Leray–Hirsch at the mapping-torus bundle

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

`cc-projective`'s `LH.lerayHirschGraded_compact` gives Leray–Hirsch for any bundle
of constant rank over a compact nonempty base.  This file instantiates it at the
projectivised sum of the mapping-torus bundle, which is the hypothesis
`LIXThomAssembly` takes.

Every input is landed: the base instances are `LIXBaseInstances`, the constant rank
is `LIXBundleModel.rank_lixBundle_plusOne`, and the positivity is free at a
successor.

**The index is `lixRank dd + 1`, not `lixRank dd`**, and that is the whole reason
this is stated at `p.plusOne`.  The fibre of `P(E ⊕ 1)` is complex projective
space of dimension the rank of `E`, so the basis has one more element than the
rank.  Produced at the bundle instead of the sum, the index would be off by one
and nothing downstream would apply — a condition checked slot by slot against
`LIXThomAssembly`.

## Main declaration

* `lixLerayHirschGraded` — Leray–Hirsch for `P(W_g ⊕ 1)` over `S¹ × S⁵ × ∏ⱼ ℂP^{dⱼ}`.
-/

open CategoryTheory
open GroupApproximation.STW59

namespace GroupApproximation.CharClass

noncomputable section

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- **Leray–Hirsch at the mapping-torus bundle.**  `cc-projective`'s compact-base
instance at the projectivised sum, with the rank supplied by
`rank_lixBundle_plusOne` and the base instances by `LIXBaseInstances`. -/
theorem lixLerayHirschGraded (G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ)
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    LerayHirschGraded
      (LH.projMapOf (lixBundle G hGc hGu).plusOne)
      (LH.tautEulerOf (lixBundle G hGc hGu).plusOne)
      (lixRank dd + 1) :=
  LH.lerayHirschGraded_compact (lixBundle G hGc hGu).plusOne (lixRank dd + 1)
    (rank_lixBundle_plusOne G hGc hGu) (Nat.succ_le_succ (Nat.zero_le _))

/-! Printed on every build. -/

#print axioms lixLerayHirschGraded

end

end GroupApproximation.CharClass
