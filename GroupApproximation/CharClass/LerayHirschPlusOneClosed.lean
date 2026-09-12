import GroupApproximation.CharClass.LerayHirschChartClass
import GroupApproximation.CharClass.LerayHirschPlusOne

/-!
# Leray–Hirsch for the projectivised sum, unconditionally

`lerayHirschGraded_plusOne` ran the cover induction with the class identification
left as a parameter, because at the time it was the one thing not proved.
`LerayHirschChartClass` proves it, so the parameter can be discharged and this is
the theorem itself.

There is no compactness and no hypothesis on the base: the cover is the diagonal
one, indexed by the finite index type of the bundle, so it is finite for free, and
the class is `tautEuler`, the Euler class of the tautological line.

This is the first half of §1.4 item 3 for an arbitrary line bundle over an
arbitrary base, and it is what the Gysin sequence is read off from.

## Main declarations

* `lerayHirschGraded_plusOne_tautEuler` — **Leray–Hirsch for `P(L ⊕ 1)`**.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace
open GroupApproximation.CharClass.Bundle

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Leray–Hirsch for `P(L ⊕ 1)`.**  `H^*(P(L ⊕ 1))` is free over `H^*(X)` on
`1` and the Euler class of the tautological line, for any line bundle `L` over any
base.  No compactness: the diagonal cover is indexed by the bundle's own finite
index type. -/
theorem lerayHirschGraded_plusOne_tautEuler [Nonempty ι] (p : Bundle X ι)
    (hp : ∀ x, (p x).trace = 1) :
    LerayHirschGraded (projMap p) (tautEuler p) 2 :=
  lerayHirschGraded_plusOne p hp (tautEuler p) fun i W =>
    pull_chartProdIso_cpTaut p (diagOpen p i ⊓ W)
      (restrictTo_trace p hp _) i (restrictTo_diag p i W)

end

end LH
end CharClass
end GroupApproximation
