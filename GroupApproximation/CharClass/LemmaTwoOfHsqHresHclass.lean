import GroupApproximation.CharClass.LIXStepCOddWired
import GroupApproximation.CharClass.LemmaTwoOddNonvanishing
import GroupApproximation.CharClass.LemmaTwoTopClass
import GroupApproximation.CharClass.LIXResFibre
import GroupApproximation.CharClass.LIXHclass
import GroupApproximation.CharClass.LIXHsq
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
one theorem.

**All three of `hsq`, `hres`, `hclass` are now discharged.**  `lix-hsq`'s `lixHsq`
(`LIXHsq.lean`), `lix-hres`'s `injective_lixRes` (`LIXResFibre.lean`) and
`lix-hclass`'s `lixHclass` (`LIXHclass.lean`) each proved exactly the residue they
were aimed at.  `lixHsq` matches this file's former `hsq` binder character for
character (same three hypotheses, same order, at `dd := LIX.lixDD j`), so its
discharge needed no instantiation at all — the plainest of the three joins.  What
follows are `LIX.LemmaTwoHolds` and `¬ ProblemLIX`, unconditionally.

**Why the composition was worth building before any of the three landed.**
`lix-hsq`, `lix-hres` and `lix-hclass` were proving these obligations
independently; if their shapes disagreed with what `lix_topClass_ne_zero_of_three`
actually consumes by so much as a degree cast or a `lixChernOf`/`lixTopClass`
unfolding, elaborating this file is where that would have surfaced.  It did surface
once already in this program — two lanes were green about different spaces for a
day.  All three discharges plugged in with no or minimal adjustment, across three
independent landings.

One check this file settled on its own: `LixChernDeg`'s codomain `Hmod2 (lixN dd) n`
and `lix_topClass_ne_zero_of_three`'s implicit `gamma : cohomologyZMod2 (lixN dd) n`
are the same object — `Hmod2 X n` is `abbrev`-equal to `cohomologyZMod2 X n`
(`CohomologyBasic.lean:48`), so no cast is needed when `gamma` is instantiated at
`lixChern (LIX.lixDD j) (mappingTorus ...) ... (lixRank (LIX.lixDD j))`.

## Main results

* `lemmaTwoHolds` --- **`LIX.LemmaTwoHolds`, unconditionally.**
* `not_problemLIX` --- **`¬ ProblemLIX`, unconditionally.**

**Kept at `#audit_axioms` here by choice, not because `#audit_closed_axioms`
would reject either declaration.**  `auditClosedAxiomsOf` (`AxiomGuard.lean:83`)
checks `(stripMData ci.type).isForall`, and `stripMData` strips only `.mdata`
wrappers — it does not unfold definitions (its own docstring says so).  So both
`lemmaTwoHolds : LIX.LemmaTwoHolds` and `not_problemLIX : ¬ ProblemLIX` here
*would* pass the closed gate: their elaborated types are, syntactically, an
application (`LIX.LemmaTwoHolds` a constant reference, `¬ ProblemLIX` a `Not`
application), not a `.forallE`, regardless of what `LIX.LemmaTwoHolds` unfolds
to.  The weaker `#audit_axioms` line is used here anyway, deliberately: this
file is internal wiring, and the single point of closed-axioms certification for
this result is the endpoint's own `¬`/`∃`-shaped statements in `ProblemLIX.lean`
— `not_problemLIX` there is a distinct declaration
(`GroupApproximation.NinetyNineProblems.not_problemLIX`) from this file's
`GroupApproximation.CharClass.not_problemLIX`.  That is the next and last step.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

/-- **`LIX.LemmaTwoHolds`, unconditionally.** -/
theorem lemmaTwoHolds : LIX.LemmaTwoHolds :=
  lemmaTwoHolds_of_oddNonvanishing fun j G hGc hGu hGe =>
    stepC_of_chain (lixChern (LIX.lixDD j))
      (fun _G' hGc' hGu' hGe' =>
        lix_topClass_ne_zero_of_three (LIX.lixDD_pos j) hGc' hGu' hGe'
          (lixHsq hGc' hGu' hGe') (injective_lixRes hGc' hGu')
          (lixHclass hGc' hGu' (continuous_mappingTorus_lix hGc')
            (isStarProjection_mappingTorus_lix hGu')))
      G hGc hGu hGe

/-- **`¬ ProblemLIX`, unconditionally.**  What remains of the answer's
dependency on algebraic topology, threaded through `not_problemLIX_of_lemmaTwo`
— nothing: it is now a theorem. -/
theorem not_problemLIX : ¬ NinetyNineProblems.ProblemLIX :=
  NinetyNineProblems.not_problemLIX_of_lemmaTwo lemmaTwoHolds

/-! ## The axiom report

Both are unconditional now, but stay at `#audit_axioms` here for the reason in
the module docstring: `#audit_closed_axioms` cannot accept a bare-`∀`-shaped
type, and the switch for the reader-facing statements belongs in
`ProblemLIX.lean`. -/

#audit_axioms lemmaTwoHolds

#audit_axioms not_problemLIX

end GroupApproximation.CharClass
