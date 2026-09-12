import GroupApproximation.CharClass.LerayHirschCompactOf
import GroupApproximation.CharClass.LerayHirschLadderClosedOf
import GroupApproximation.Meta.AxiomGuard

/-!
# Leray–Hirsch for a projectivised bundle over a compact base, over a field, unconditionally

`LerayHirschCompactOf.lerayHirschGraded_compactOf_of_freeTuple` asks for the free tuple of
`U × ℂP^{d+1}` with a nonzero fibre class in the ranks it uses, and
`LerayHirschLadderClosedOf.hasFreeTuple_cpProdOf` supplies it for every rank, its ring input being
`ProjectiveSpaceRingClosedOf.cupPowE_ne_zeroOf`.  So Leray–Hirsch over a compact base holds over every
field, for every nonzero class `hgen`, at every rank, with no hypothesis, and so does its dual form.

## Main declarations

* `lerayHirschGraded_compactOf` — **Leray–Hirsch over a compact base, over a field**.
* `lerayHirschGraded_compactDualOf` — the same for `tautEulerDualK`, the class of the splitting
  principle.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory TopologicalSpace
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle

noncomputable section

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Leray–Hirsch for a projectivised bundle over a compact base, over a field**, at every rank and
for every nonzero class `hgen ∈ H^2(ℂP^{1 + card ι}; K)`.  `H^*(P(q); K)` is free over `H^*(X; K)` on
the powers of the tautological class. -/
theorem lerayHirschGraded_compactOf (K : Type) [Field K] [CompactSpace X] [Nonempty X]
    (q : Bundle X ι) (s : ℕ) (hs : ∀ x, q.rank x = s) (hs1 : 1 ≤ s)
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2) (hgen0 : hgen ≠ 0) :
    LerayHirschGraded (projMapOf q) (tautEulerOfK K hgen q) s :=
  lerayHirschGraded_compactOf_of_freeTuple K q s hs hs1 hgen hgen0
    (by
      intro U _ d _ hfib hfib0
      exact hasFreeTuple_cpProdOf K U d (by omega) hfib hfib0)

/-- **Leray–Hirsch over a compact base for the dual tautological class**, over a field. -/
theorem lerayHirschGraded_compactDualOf (K : Type) [Field K] [CompactSpace X] [Nonempty X]
    (q : Bundle X ι) (s : ℕ) (hs : ∀ x, q.rank x = s) (hs1 : 1 ≤ s)
    (hgen : Hmod K (CPtop (1 + tautCardOf ι)) 2) (hgen0 : hgen ≠ 0) :
    LerayHirschGraded (projMapOf q) (tautEulerDualK K hgen q) s :=
  lerayHirschGraded_neg (lerayHirschGraded_compactOf K q s hs hs1 hgen hgen0)

end

#audit_axioms lerayHirschGraded_compactOf
#audit_axioms lerayHirschGraded_compactDualOf

end LH
end CharClass
end GroupApproximation
