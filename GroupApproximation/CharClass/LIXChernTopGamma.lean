import GroupApproximation.CharClass.LIXThomClassTerm
import GroupApproximation.CharClass.LerayHirschGammaIso
import GroupApproximation.CharClass.ChernGammaComponent
import GroupApproximation.CharClass.LIXChernValue

/-!
# The endgame's top Chern class, as a coefficient of this lane's instance

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C).

The `gamma` that `lix_topClass_ne_zero_of_local` and `ThomChainThom` consume is
`lixChern` at the rank, which is `cc-projective`'s **ring-level** Chern class read
in one degree.  The Thom class is characterised by the **degreewise**
coefficients of the instance transported onto the hyperplane.  Three landed facts
turn the first into the second, and this file composes them.

* `lixChern_mappingTorus` (`cc-projective`) — the branch is taken, so `gamma` is
  `TotalH.component` of `.chern`.
* `LH.component_chern_eq_gamma` (`cc-projective`) — that component **is**
  `LerayHirschGraded.gamma`.
* `LH.gamma_of_iso` (this lane) — the transport onto the hyperplane leaves it
  alone.

## What this is and is not

It is the half of `hclass` that mentions no free binder, finished.

It is **not** `hclass`.  That equation is `jE.hom u = piStar.hom gamma`, and `jE`,
`piStar` and their common object are still free binders in `cc-lix-odd`'s
theorem; until they are concrete terms there is nothing to prove, and the
statement is false for arbitrary maps satisfying only the naturality and
splitting hypotheses.  What is finished here is that both sides of `hclass` may
now be spoken about in **one** description of the top class instead of two.

## Main declaration

* `lixChern_top_eq_gamma` — the endgame's `gamma` is `lixLHhyper`'s top Chern class.
-/

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

open ThomChernDeg LH

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-- **The endgame's top Chern class is the top Chern class of this lane's
instance.**  Ring-level to degreewise by `cc-projective`'s bridge, then across the
transport onto the hyperplane by `gamma_of_iso`. -/
theorem lixChern_top_eq_gamma (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (hcont : Continuous (mappingTorus Vmat G circHoriz circHeight))
    (hproj : ∀ p, IsStarProjection (mappingTorus Vmat G circHoriz circHeight p)) :
    lixChern dd (mappingTorus Vmat G circHoriz circHeight) hcont hproj (lixRank dd)
      = (lixLHhyper hGc hGu).gamma (lixRank dd) := by
  refine (lixChern_mappingTorus G hGc hGu hcont hproj (lixRank dd)).trans ?_
  refine (LH.component_chern_eq_gamma
    (lerayHirschGraded_compact (lixBundle G hGc hGu) (lixRank dd)
      (rank_lixBundle G hGc hGu) (one_le_lixRank_dd dd)) (lixRank dd)).trans ?_
  exact LH.gamma_of_iso (hyperIso (lixBundle G hGc hGu))
    (projMapOf (lixBundle G hGc hGu)) (hyperProj (lixBundle G hGc hGu))
    (hyperIso_hom_comp (lixBundle G hGc hGu)) (tautEulerOf (lixBundle G hGc hGu))
    (tautEulerRange (lixBundle G hGc hGu)) rfl
    (lerayHirschGraded_compact (lixBundle G hGc hGu) (lixRank dd)
      (rank_lixBundle G hGc hGu) (one_le_lixRank_dd dd)) (lixRank dd)

/-! Printed on every build. -/

#print axioms lixChern_top_eq_gamma

end

end GroupApproximation.CharClass
