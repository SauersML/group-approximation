import GroupApproximation.CharClass.LIXStepCOddWired
import GroupApproximation.CharClass.LemmaTwoOddNonvanishing
import GroupApproximation.CharClass.LemmaTwoTopClass
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemLIX
import GroupApproximation.Meta.AxiomGuard

/-!
# `LIXStepCOddWired` and `LemmaTwoOddNonvanishing`, threaded into one theorem

Lane `cs-endpoint` of the STW Problem LIX program.

`LIXStepCOddWired.lean`'s `lix_topClass_ne_zero_of_three` produces `gamma ≠ 0` for a
`gamma` the caller instantiates via `hclass`.  `LemmaTwoOddNonvanishing.lean`'s
`lemmaTwoHolds_of_oddNonvanishing` consumes an already-`lixTopClass`-wrapped
nonvanishing.  Between them sits `LemmaTwoTopClass.lean`'s `stepC_of_chain`, which
takes the raw, per-`G` nonvanishing and wraps it.  This file threads all three into
one theorem, taking exactly `hsq`, `hres`, `hclass` (universally quantified over
every stage `j` and every Step A unitary `G`) and concluding `LIX.LemmaTwoHolds`,
then `¬ ProblemLIX`.

**Why this is worth building before the three land, not after.**  `lix-hsq`,
`lix-hres` and `lix-hclass` are proving these three obligations independently; if
their shapes disagree with what `lix_topClass_ne_zero_of_three` actually consumes
by so much as a degree cast or a `lixChernOf`/`lixTopClass` unfolding, elaborating
this file is where that surfaces.  It did surface once already in this program —
two lanes were green about different spaces for a day — so the composition is
tested here, with `hsq`/`hres`/`hclass` as open hypotheses, rather than left for the
day the three obligations land.

One check this file settles on its own: `LixChernDeg`'s codomain `Hmod2 (lixN dd) n`
and `lix_topClass_ne_zero_of_three`'s implicit `gamma : cohomologyZMod2 (lixN dd) n`
are the same object — `Hmod2 X n` is `abbrev`-equal to `cohomologyZMod2 X n`
(`CohomologyBasic.lean:48`), so no cast is needed when `gamma` is instantiated at
`lixChern (LIX.lixDD j) (mappingTorus ...) ... (lixRank (LIX.lixDD j))`.

## Main results

* `lemmaTwoHolds_of_hsq_hres_hclass` --- **`LIX.LemmaTwoHolds`, over the three.**
* `not_problemLIX_of_hsq_hres_hclass` --- **`¬ ProblemLIX`, over the three.**

**Kept at `#audit_axioms`.**  All three hypotheses are open, so nothing here may
claim `#audit_closed_axioms` until `lix-hsq`, `lix-hres` and `lix-hclass` land.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

/-- **`LIX.LemmaTwoHolds`, from `hsq`, `hres` and `hclass` at every stage.**  `hres`
and `hclass` do not depend on the Step A witness `hGe`, matching exactly what
`lix_topClass_ne_zero_of_three` itself asks of them. -/
theorem lemmaTwoHolds_of_hsq_hres_hclass
    (hsq : ∀ j : ℕ,
      ∀ (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
        (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
        (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0),
        lixSRel hGc hGu hGe (2 * lixRank (LIX.lixDD j))
            ≫ (lixRelModelIso (LIX.lixDD j) (2 * lixRank (LIX.lixDD j))).hom
          = lixRes hGc hGu (2 * lixRank (LIX.lixDD j))
              ≫ (lixLocalPairIsoClosed hGc hGu).hom)
    (hres : ∀ j : ℕ,
      ∀ (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
        (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
        Function.Injective (lixRes hGc hGu (2 * lixRank (LIX.lixDD j))).hom)
    (hclass : ∀ j : ℕ,
      ∀ (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
        (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
        (RelativeSupport.lixJE hGc hGu (2 * lixRank (LIX.lixDD j))).hom
            (lixThomClassTerm hGc hGu)
          = (RelativeSupport.lixPiStar hGc hGu (2 * lixRank (LIX.lixDD j))).hom
              (lixChern (LIX.lixDD j) (mappingTorus Vmat G circHoriz circHeight)
                (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu)
                (lixRank (LIX.lixDD j)))) :
    LIX.LemmaTwoHolds :=
  lemmaTwoHolds_of_oddNonvanishing fun j G hGc hGu hGe =>
    stepC_of_chain (lixChern (LIX.lixDD j))
      (fun G' hGc' hGu' hGe' =>
        lix_topClass_ne_zero_of_three (LIX.lixDD_pos j) hGc' hGu' hGe'
          (hsq j G' hGc' hGu' hGe') (hres j G' hGc' hGu') (hclass j G' hGc' hGu'))
      G hGc hGu hGe

/-- **`¬ ProblemLIX`, from `hsq`, `hres` and `hclass` at every stage.**  The whole
dependency of the answer on algebraic topology, threaded through
`not_problemLIX_of_lemmaTwo`. -/
theorem not_problemLIX_of_hsq_hres_hclass
    (hsq : ∀ j : ℕ,
      ∀ (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
        (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
        (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0),
        lixSRel hGc hGu hGe (2 * lixRank (LIX.lixDD j))
            ≫ (lixRelModelIso (LIX.lixDD j) (2 * lixRank (LIX.lixDD j))).hom
          = lixRes hGc hGu (2 * lixRank (LIX.lixDD j))
              ≫ (lixLocalPairIsoClosed hGc hGu).hom)
    (hres : ∀ j : ℕ,
      ∀ (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
        (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
        Function.Injective (lixRes hGc hGu (2 * lixRank (LIX.lixDD j))).hom)
    (hclass : ∀ j : ℕ,
      ∀ (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
        (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
        (RelativeSupport.lixJE hGc hGu (2 * lixRank (LIX.lixDD j))).hom
            (lixThomClassTerm hGc hGu)
          = (RelativeSupport.lixPiStar hGc hGu (2 * lixRank (LIX.lixDD j))).hom
              (lixChern (LIX.lixDD j) (mappingTorus Vmat G circHoriz circHeight)
                (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu)
                (lixRank (LIX.lixDD j)))) :
    ¬ NinetyNineProblems.ProblemLIX :=
  NinetyNineProblems.not_problemLIX_of_lemmaTwo
    (lemmaTwoHolds_of_hsq_hres_hclass hsq hres hclass)

/-! ## The axiom report

Both hypotheses are open, so these stay at `#audit_axioms`: neither may claim
`#audit_closed_axioms` until `lix-hsq`, `lix-hres` and `lix-hclass` land. -/

#audit_axioms lemmaTwoHolds_of_hsq_hres_hclass

#audit_axioms not_problemLIX_of_hsq_hres_hclass

end GroupApproximation.CharClass
