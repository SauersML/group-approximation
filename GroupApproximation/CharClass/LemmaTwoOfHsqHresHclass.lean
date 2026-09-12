import GroupApproximation.CharClass.LIXStepCOddWired
import GroupApproximation.CharClass.LemmaTwoOddNonvanishing
import GroupApproximation.CharClass.LemmaTwoTopClass
import GroupApproximation.CharClass.LIXResFibre
import GroupApproximation.CharClass.LIXHclass
import GroupApproximation.CharClass.LIXHsq
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
follows is `LIX.LemmaTwoHolds`, unconditionally.

**No `¬ ProblemLIX` corollary here, deliberately.**  An earlier version of this
file also derived `not_problemLIX` by applying `NinetyNineProblems.not_problemLIX_of_lemmaTwo`
to `lemmaTwoHolds`, which needed importing `Manuscript/NinetyNineProblems/ProblemLIX.lean`.
Once that file was edited to import `lemmaTwoHolds` back (to state its own bare
`not_problemLIX`), the two imports formed a build cycle — caught by the probe, not
by inspection.  The fix is directional: this file supplies `LIX.LemmaTwoHolds`
and nothing about `ProblemLIX`, and `ProblemLIX.lean` is the only place that
combines the two, exactly as `not_problemLIX_of_lemmaTwo`'s own signature already
implied it should be.

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

## Main result

* `lemmaTwoHolds` --- **`LIX.LemmaTwoHolds`, unconditionally.**

**Kept at `#audit_axioms` here by choice, not because `#audit_closed_axioms`
would reject it.**  `auditClosedAxiomsOf` (`AxiomGuard.lean:83`) checks
`(stripMData ci.type).isForall`, and `stripMData` strips only `.mdata`
wrappers — it does not unfold definitions (its own docstring says so).  So
`lemmaTwoHolds : LIX.LemmaTwoHolds` *would* pass the closed gate: its
elaborated type is, syntactically, a constant reference, not a `.forallE`,
regardless of what `LIX.LemmaTwoHolds` unfolds to.  The weaker `#audit_axioms`
line is used here anyway, deliberately: this file is internal wiring, and the
single point of closed-axioms certification for this result is the endpoint's
own `¬`/`∃`-shaped statements in `ProblemLIX.lean`, which is also the only
place `¬ ProblemLIX` is derived from `lemmaTwoHolds` — see the note above on
why that combination does not live here.
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

/-! ## The axiom report

Unconditional now, but stays at `#audit_axioms` here for the reason in the
module docstring: the switch for the reader-facing statements belongs in
`ProblemLIX.lean`, which derives `¬ ProblemLIX` from this theorem. -/

#audit_axioms lemmaTwoHolds

end GroupApproximation.CharClass
