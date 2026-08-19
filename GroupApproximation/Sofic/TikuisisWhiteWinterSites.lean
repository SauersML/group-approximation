import GroupApproximation.Analysis.TikuisisWhiteWinter
import GroupApproximation.Sofic.CliffordAsideInert
import GroupApproximation.Sofic.LiteralTraceConsequence

/-!
# The two sites of the Tikuisis--White--Winter citation, and what the
manuscript's own theorem says back to it

`Analysis.TikuisisWhiteWinter` states the theorem and reduces the printed
implication `amenable ⟹ operator-MF` to it, at every countable group.  This
file lands that reduction at the two places the manuscript uses it, and then
runs it backwards at the group the manuscript constructs.

## `CY.12c`: the sharpness aside

`isOperatorMF_realizedQuotient_of_tww` is the aside, over the inputs it rests
on rather than over the group implication as a whole.  Its subject is amenable
with no hypothesis (`CliffordAsideInert.realizedQuotient_isAmenable`, which is
`CY.12b`), so the entire content of the aside is the three C⋆-algebraic
inputs.

`Sofic.CliffordAsideInert.aside_inert` already proves that deleting the aside
changes no conclusion of the paragraph, and nothing here weakens that: the
sharpness paragraph's own conclusion is proved with no hypothesis in
`Sofic.CliffordQuotientMFUnconditional`.  What this file adds is the other
half of the accounting --- if a reader *does* want the aside, this is exactly
what it costs.

`isOperatorMF_realizedQuotient_of_quasidiagonalTrace` sharpens the cost
further, in the same style as
`CliffordAsideInert.isOperatorMF_realizedQuotient_of_local`: the site does not
need the general theorem, only quasidiagonality of one trace on one algebra.

## `INT.17`, backwards: the manuscript's group is a non-quasidiagonal trace

Theorem A produces a countable group `E` that is not operator-MF, and
`Sofic.LiteralTraceConsequence` turns that into: the canonical trace of
`C⋆(E)` is not an MF trace.  Running the route of
`Analysis.TikuisisWhiteWinter` backwards through that gives two statements
that are new here, and both are unconditional in the interesting variable:

* `markedGroup_canonicalReducedTrace_not_isQuasidiagonalTrace` --- the
  canonical *faithful* trace of `C⋆_r(E)` is **not quasidiagonal**.  A
  faithful non-quasidiagonal trace on a separable C⋆-algebra is exactly what
  Tikuisis--White--Winter forbids under nuclearity and the UCT, so this is the
  sharp form of "the manuscript's algebra is far from the TWW hypotheses".
* `markedGroup_reducedGroupCStar_not_isNuclear_of_tww` --- **granting
  Tikuisis--White--Winter and the UCT for that one algebra, `C⋆_r(E)` is not
  nuclear.**

The second is worth reading twice.  Non-nuclearity of `C⋆_r(E)` is what row
`RE.05` prints, and the repository's only route to it is
`NuclearityAmenability.reducedGroupCStar_not_isNuclearCStar_of_lance` ---
through Lance's theorem, and at the *other* nuclearity predicate
(`CStarTensor.IsNuclearCStar`, the `min = max` one).  This is an independent
route to the same conclusion at the CPAP predicate, and it consumes a
different literature input.  Neither route is discharged; having two of them
means the claim does not rest on a single citation.

**Nothing here inhabits any input.**
-/

namespace GroupApproximation
namespace TikuisisWhiteWinterSites

open LiteralNonMFPresentation ReducedGroupCStarTrace

noncomputable section

/-! ## `CY.12c`: the aside in the sharpness paragraph -/

/-- **The site needs only one quasidiagonal trace.**  If the canonical trace
of the reduced C⋆-algebra of the realized Clifford quotient is quasidiagonal,
that group is operator-MF.

This is `QuasidiagonalMF.isOperatorMF_of_isQuasidiagonalCanonicalTrace` at the
one group, and it is the precise analogue of
`CliffordAsideInert.isOperatorMF_realizedQuotient_of_local`: the aside is one
instance of a general clause, and the instance is far smaller than the
clause. -/
theorem isOperatorMF_realizedQuotient_of_quasidiagonalTrace
    (hucp : Quasidiagonal.UCPContractive.{0})
    (h : Quasidiagonal.IsQuasidiagonalTrace
      (fun T : ReducedGroupCStar LiteralCyclicCalibration.RealizedQuotient ↦
        ReducedGroupCStarTrace.canonicalFaithfulTracialState
          LiteralCyclicCalibration.RealizedQuotient T)) :
    IsOperatorMF LiteralCyclicCalibration.RealizedQuotient :=
  QuasidiagonalMF.isOperatorMF_of_isQuasidiagonalCanonicalTrace hucp
    LiteralCyclicCalibration.RealizedQuotient h

/-- **`CY.12c` over the inputs it rests on.**  Granting the ucp facts,
Tikuisis--White--Winter, Lance and Tu, the realized Clifford quotient is
operator-MF.

The amenability half of the printed sentence is discharged
(`CliffordAsideInert.realizedQuotient_isAmenable`), so the three C⋆-algebraic
inputs are the entire external content of the aside --- previously recorded as
the single opaque binder `CyclicBaseCalibration.AmenableImpliesMF`. -/
theorem isOperatorMF_realizedQuotient_of_tww {UCT : Type → Prop}
    (hucp : Quasidiagonal.UCPContractive.{0})
    (tww : QuasidiagonalMF.TikuisisWhiteWinterInput UCT)
    (lance : QuasidiagonalMF.AmenableNuclearInput.{0})
    (tu : QuasidiagonalMF.AmenableUCTInput.{0} UCT) :
    IsOperatorMF LiteralCyclicCalibration.RealizedQuotient :=
  QuasidiagonalMF.isOperatorMF_of_isAmenable_of_tww hucp tww lance tu
    LiteralCyclicCalibration.RealizedQuotient
    CliffordAsideInert.realizedQuotient_isAmenable

/-! ## The manuscript's group, read against the theorem it cites -/

/-- **The canonical faithful trace of `C⋆_r(E)` is not quasidiagonal.**

`E` is the marked group of Theorem A.  It is not operator-MF, so by the
reduction half of `INT.11` --- which is proved --- no quasidiagonal trace can
sit on the reduced algebra at the canonical functional.  The trace in question
*is* faithful and the algebra *is* separable, both proved here, so this is a
faithful non-quasidiagonal trace on a separable C⋆-algebra: the exact
configuration Tikuisis--White--Winter shows is impossible for nuclear UCT
algebras.

The only external content is the ucp facts, which are dischargeable in-repo;
in particular this does **not** depend on Tikuisis--White--Winter. -/
theorem markedGroup_canonicalReducedTrace_not_isQuasidiagonalTrace
    (hucp : Quasidiagonal.UCPContractive.{0}) :
    ¬ Quasidiagonal.IsQuasidiagonalTrace
      (fun T : ReducedGroupCStar MarkedGroup ↦
        ReducedGroupCStarTrace.canonicalFaithfulTracialState MarkedGroup T) := by
  intro h
  exact LiteralTraceConsequence.markedGroup_canonicalMaximalTrace_not_isMFTrace
    (ShulmanTrace.isMFTrace_canonicalMaximal_of_reducedTrace MarkedGroup
      (Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace hucp h))

/-- **A second route to `RE.05`.**  Granting Tikuisis--White--Winter, and the
UCT for this one algebra, the reduced C⋆-algebra of the marked group is not
nuclear.

The four hypotheses of the theorem are met by two theorems and one assumption:
separability and faithfulness are proved
(`reducedGroupCStar_separableSpace`, `canonicalFaithfulTracialState`), the UCT
is assumed for this algebra alone, and nuclearity is what gets refuted.  The
contradiction is with Theorem A, through
`markedGroup_canonicalReducedTrace_not_isQuasidiagonalTrace`.

This is not the repository's existing route to non-nuclearity, which runs
through Lance's theorem at the `min = max` predicate
(`NuclearityAmenability.reducedGroupCStar_not_isNuclearCStar_of_lance`).  The
two are independent: different predicate, different citation.  Neither is
discharged. -/
theorem markedGroup_reducedGroupCStar_not_isNuclear_of_tww {UCT : Type → Prop}
    (hucp : Quasidiagonal.UCPContractive.{0})
    (tww : QuasidiagonalMF.TikuisisWhiteWinterInput UCT)
    (huct : UCT (ReducedGroupCStar MarkedGroup)) :
    ¬ CStarExactness.IsNuclearCStarAlgebra (ReducedGroupCStar MarkedGroup) := by
  intro hnuc
  refine markedGroup_canonicalReducedTrace_not_isQuasidiagonalTrace hucp ?_
  exact tww.quasidiagonalTrace (ReducedGroupCStar MarkedGroup) inferInstance
    (ReducedGroupCStarTrace.reducedGroupCStar_separableSpace MarkedGroup) hnuc
    huct (ReducedGroupCStarTrace.canonicalFaithfulTracialState MarkedGroup)

end

end TikuisisWhiteWinterSites
end GroupApproximation
