import GroupApproximation.CharClass.LIXStepCOddWired
import GroupApproximation.CharClass.LemmaTwoOddNonvanishing
import GroupApproximation.CharClass.LemmaTwoTopClass
import GroupApproximation.CharClass.LIXResFibre
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
one theorem, taking `hsq` and `hclass` (universally quantified over every stage `j`
and every Step A unitary `G`) and concluding `LIX.LemmaTwoHolds`, then
`¬ ProblemLIX`.

**`hres` is discharged.**  `lix-hres`'s `injective_lixRes`
(`LIXResFibre.lean`) proves exactly the third residue, with no hypothesis beyond
`hGc`/`hGu`, so this file no longer takes it as an argument.  This is the first of
the three intermediate forms; `hsq` and `hclass` remain open.

**Why the composition was worth building before any of the three landed.**
`lix-hsq`, `lix-hres` and `lix-hclass` are proving these obligations
independently; if their shapes disagree with what `lix_topClass_ne_zero_of_three`
actually consumes by so much as a degree cast or a `lixChernOf`/`lixTopClass`
unfolding, elaborating this file is where that surfaces.  It did surface once
already in this program — two lanes were green about different spaces for a day.
`hres`'s discharge below is the first confirmation that the join really is
tight: `injective_lixRes` plugs in with no adjustment.

One check this file settles on its own: `LixChernDeg`'s codomain `Hmod2 (lixN dd) n`
and `lix_topClass_ne_zero_of_three`'s implicit `gamma : cohomologyZMod2 (lixN dd) n`
are the same object — `Hmod2 X n` is `abbrev`-equal to `cohomologyZMod2 X n`
(`CohomologyBasic.lean:48`), so no cast is needed when `gamma` is instantiated at
`lixChern (LIX.lixDD j) (mappingTorus ...) ... (lixRank (LIX.lixDD j))`.

## Main results

* `lemmaTwoHolds_of_hsq_hclass` --- **`LIX.LemmaTwoHolds`, over the remaining two.**
* `not_problemLIX_of_hsq_hclass` --- **`¬ ProblemLIX`, over the remaining two.**

**Kept at `#audit_axioms`.**  `hsq` and `hclass` are still open, so nothing here
may claim `#audit_closed_axioms` until `lix-hsq` and `lix-hclass` land too.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

/-- **`LIX.LemmaTwoHolds`, from `hsq` and `hclass` at every stage.**  `hclass`
does not depend on the Step A witness `hGe`, matching exactly what
`lix_topClass_ne_zero_of_three` itself asks of it. -/
theorem lemmaTwoHolds_of_hsq_hclass
    (hsq : ∀ j : ℕ,
      ∀ (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
        (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
        (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0),
        lixSRel hGc hGu hGe (2 * lixRank (LIX.lixDD j))
            ≫ (lixRelModelIso (LIX.lixDD j) (2 * lixRank (LIX.lixDD j))).hom
          = lixRes hGc hGu (2 * lixRank (LIX.lixDD j))
              ≫ (lixLocalPairIsoClosed hGc hGu).hom)
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
          (hsq j G' hGc' hGu' hGe') (injective_lixRes hGc' hGu')
          (hclass j G' hGc' hGu'))
      G hGc hGu hGe

/-- **`¬ ProblemLIX`, from `hsq` and `hclass` at every stage.**  What remains of
the answer's dependency on algebraic topology, threaded through
`not_problemLIX_of_lemmaTwo`. -/
theorem not_problemLIX_of_hsq_hclass
    (hsq : ∀ j : ℕ,
      ∀ (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
        (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
        (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0),
        lixSRel hGc hGu hGe (2 * lixRank (LIX.lixDD j))
            ≫ (lixRelModelIso (LIX.lixDD j) (2 * lixRank (LIX.lixDD j))).hom
          = lixRes hGc hGu (2 * lixRank (LIX.lixDD j))
              ≫ (lixLocalPairIsoClosed hGc hGu).hom)
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
    (lemmaTwoHolds_of_hsq_hclass hsq hclass)

/-! ## The axiom report

Both hypotheses are open, so these stay at `#audit_axioms`: neither may claim
`#audit_closed_axioms` until `lix-hsq` and `lix-hclass` land. -/

#audit_axioms lemmaTwoHolds_of_hsq_hclass

#audit_axioms not_problemLIX_of_hsq_hclass

end GroupApproximation.CharClass
