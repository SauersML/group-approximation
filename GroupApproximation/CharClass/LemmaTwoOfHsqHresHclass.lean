import GroupApproximation.CharClass.LIXStepCOddWired
import GroupApproximation.CharClass.LemmaTwoOddNonvanishing
import GroupApproximation.CharClass.LemmaTwoTopClass
import GroupApproximation.CharClass.LIXResFibre
import GroupApproximation.CharClass.LIXHclass
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
one theorem, taking `hsq` (universally quantified over every stage `j` and every
Step A unitary `G`) and concluding `LIX.LemmaTwoHolds`, then `¬ ProblemLIX`.

**`hres` and `hclass` are both discharged.**  `lix-hres`'s `injective_lixRes`
(`LIXResFibre.lean`) and `lix-hclass`'s `lixHclass` (`LIXHclass.lean`) each proved
exactly the residue they were aimed at, with no hypothesis beyond `hGc`/`hGu` (and,
for `lixHclass`, the two proof arguments this file's binder pinned, which their
theorem generalises — a fit, not a mismatch).  `hsq` is the only hypothesis left.

**Why the composition was worth building before any of the three landed.**
`lix-hsq`, `lix-hres` and `lix-hclass` were proving these obligations
independently; if their shapes disagreed with what `lix_topClass_ne_zero_of_three`
actually consumes by so much as a degree cast or a `lixChernOf`/`lixTopClass`
unfolding, elaborating this file is where that would have surfaced.  It did surface
once already in this program — two lanes were green about different spaces for a
day.  Two of the three discharges below plugged in with no adjustment; that is the
join staying tight across two independent landings.

One check this file settled on its own: `LixChernDeg`'s codomain `Hmod2 (lixN dd) n`
and `lix_topClass_ne_zero_of_three`'s implicit `gamma : cohomologyZMod2 (lixN dd) n`
are the same object — `Hmod2 X n` is `abbrev`-equal to `cohomologyZMod2 X n`
(`CohomologyBasic.lean:48`), so no cast is needed when `gamma` is instantiated at
`lixChern (LIX.lixDD j) (mappingTorus ...) ... (lixRank (LIX.lixDD j))`.

## Main results

* `lemmaTwoHolds_of_hsq` --- **`LIX.LemmaTwoHolds`, over the last one.**
* `not_problemLIX_of_hsq` --- **`¬ ProblemLIX`, over the last one.**

**Kept at `#audit_axioms`.**  `hsq` is still open, so nothing here may claim
`#audit_closed_axioms` until `lix-hsq` lands too.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

/-- **`LIX.LemmaTwoHolds`, from `hsq` alone at every stage.** -/
theorem lemmaTwoHolds_of_hsq
    (hsq : ∀ j : ℕ,
      ∀ (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
        (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
        (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0),
        lixSRel hGc hGu hGe (2 * lixRank (LIX.lixDD j))
            ≫ (lixRelModelIso (LIX.lixDD j) (2 * lixRank (LIX.lixDD j))).hom
          = lixRes hGc hGu (2 * lixRank (LIX.lixDD j))
              ≫ (lixLocalPairIsoClosed hGc hGu).hom) :
    LIX.LemmaTwoHolds :=
  lemmaTwoHolds_of_oddNonvanishing fun j G hGc hGu hGe =>
    stepC_of_chain (lixChern (LIX.lixDD j))
      (fun G' hGc' hGu' hGe' =>
        lix_topClass_ne_zero_of_three (LIX.lixDD_pos j) hGc' hGu' hGe'
          (hsq j G' hGc' hGu' hGe') (injective_lixRes hGc' hGu')
          (lixHclass hGc' hGu' (continuous_mappingTorus_lix hGc')
            (isStarProjection_mappingTorus_lix hGu')))
      G hGc hGu hGe

/-- **`¬ ProblemLIX`, from `hsq` alone at every stage.**  What remains of the
answer's dependency on algebraic topology, threaded through
`not_problemLIX_of_lemmaTwo`. -/
theorem not_problemLIX_of_hsq
    (hsq : ∀ j : ℕ,
      ∀ (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
        (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
        (hGe : ∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0),
        lixSRel hGc hGu hGe (2 * lixRank (LIX.lixDD j))
            ≫ (lixRelModelIso (LIX.lixDD j) (2 * lixRank (LIX.lixDD j))).hom
          = lixRes hGc hGu (2 * lixRank (LIX.lixDD j))
              ≫ (lixLocalPairIsoClosed hGc hGu).hom) :
    ¬ NinetyNineProblems.ProblemLIX :=
  NinetyNineProblems.not_problemLIX_of_lemmaTwo (lemmaTwoHolds_of_hsq hsq)

/-! ## The axiom report

`hsq` is still open, so this stays at `#audit_axioms`: it may not claim
`#audit_closed_axioms` until `lix-hsq` lands. -/

#audit_axioms lemmaTwoHolds_of_hsq

#audit_axioms not_problemLIX_of_hsq

end GroupApproximation.CharClass
