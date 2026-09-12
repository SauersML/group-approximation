import GroupApproximation.Analysis.TikuisisWhiteWinterUnconditional
import GroupApproximation.Sofic.TikuisisWhiteWinterSites

/-!
# The two sites again, with the ucp binder gone, and TWW's hypotheses shown
sharp

`Sofic.TikuisisWhiteWinterSites` lands the Tikuisis--White--Winter reduction at
the manuscript's two citation sites and runs it backwards at the group of
Theorem A.  Every statement there carries a hypothesis
`Quasidiagonal.UCPContractive` --- that a unital completely positive map into a
matrix algebra is a contraction --- because at the time it was written that
fact was a typed input.

It is a theorem now (`Quasidiagonal.ucpContractive`, off this repository's
Stinespring dilation).  This file discharges the binder at each site, and
records what the discharged form says about Tikuisis--White--Winter itself.

## What the marked group says back to the theorem

`markedGroup_canonicalReducedTrace_not_isQuasidiagonalTrace_unconditional` is
now a theorem with **no hypotheses at all**:

> the canonical faithful trace of `C⋆_r(E)` is not quasidiagonal,

for `E` the group of Theorem A.  Together with separability of that algebra
(`reducedGroupCStar_separableSpace`, proved) and faithfulness of that trace
(`canonicalFaithfulTracialState`, proved), this is an unconditional exhibition
of the configuration

> a faithful trace on a separable C⋆-algebra which is **not** quasidiagonal,

which is exactly what Tikuisis--White--Winter forbids once nuclearity and the
UCT are added.  So the two hypotheses of that theorem are not decoration: this
repository now proves, with no input, that dropping them makes the conclusion
false.  `Analysis.CompressionTraceLocallyFinite` proves the conclusion
unconditionally on the locally finite groups; between the two, both sides of
the theorem's boundary are machine-checked, and what is left in the middle is
the theorem.

## What is still assumed

`markedGroup_reducedGroupCStar_not_isNuclear_of_twwInput` keeps
Tikuisis--White--Winter and a UCT hypothesis for the one algebra: it is the
route to `RE.05` that goes through quasidiagonality, and it is conditional by
design.  Nothing here inhabits `QuasidiagonalMF.TikuisisWhiteWinterInput`.

## Manuscript status

No ledger grade moves.  `RE.05` keeps its existing route
(`NuclearityAmenability.reducedGroupCStar_not_isNuclearCStar_of_lance`); this
file shortens the *other* route's input list by one.
-/

namespace GroupApproximation
namespace TikuisisWhiteWinterSites

open LiteralNonMFPresentation ReducedGroupCStarTrace

noncomputable section

/-! ## `CY.12c`, with the ucp binder discharged -/

/-- **The aside, at the one trace it needs.**  If the canonical trace of the
reduced algebra of the realized Clifford quotient is quasidiagonal, that group
is operator-MF --- with no further input. -/
theorem isOperatorMF_realizedQuotient_of_quasidiagonalTrace_unconditional
    (h : Quasidiagonal.IsQuasidiagonalTrace
      (fun T : ReducedGroupCStar LiteralCyclicCalibration.RealizedQuotient ↦
        ReducedGroupCStarTrace.canonicalFaithfulTracialState
          LiteralCyclicCalibration.RealizedQuotient T)) :
    IsOperatorMF LiteralCyclicCalibration.RealizedQuotient :=
  isOperatorMF_realizedQuotient_of_quasidiagonalTrace
    Quasidiagonal.ucpContractive h

/-- **`CY.12c` over three inputs instead of four.**  The ucp facts are gone;
Tikuisis--White--Winter, Lance and Tu remain in the type.  (Lance is a theorem
elsewhere in the tree and Tu is eliminable; see
`Analysis.TikuisisWhiteWinterAmenableClass`, which does both at once.) -/
theorem isOperatorMF_realizedQuotient_of_twwInput {UCT : Type → Prop}
    (tww : QuasidiagonalMF.TikuisisWhiteWinterInput UCT)
    (lance : QuasidiagonalMF.AmenableNuclearInput.{0})
    (tu : QuasidiagonalMF.AmenableUCTInput.{0} UCT) :
    IsOperatorMF LiteralCyclicCalibration.RealizedQuotient :=
  isOperatorMF_realizedQuotient_of_tww Quasidiagonal.ucpContractive tww lance tu

/-! ## The sharpness of the theorem's hypotheses -/

/-- **A faithful non-quasidiagonal trace, unconditionally.**

No hypotheses: the ucp binder is discharged by `Quasidiagonal.ucpContractive`,
and everything else was already proved.  This is Theorem A read as a statement
about traces. -/
theorem markedGroup_canonicalReducedTrace_not_isQuasidiagonalTrace_unconditional :
    ¬ Quasidiagonal.IsQuasidiagonalTrace
      (fun T : ReducedGroupCStar MarkedGroup ↦
        ReducedGroupCStarTrace.canonicalFaithfulTracialState MarkedGroup T) :=
  markedGroup_canonicalReducedTrace_not_isQuasidiagonalTrace
    Quasidiagonal.ucpContractive

/-- **The hypotheses of Tikuisis--White--Winter are sharp**, in the only sense
this repository can express without formalizing nuclearity theory: there is a
separable C⋆-algebra carrying a faithful trace that is not quasidiagonal.

Faithfulness is not stated as a separate clause because it is built into the
object: `canonicalFaithfulTracialState` is a `FaithfulTracialState` by
construction.  Both clauses below are unconditional. -/
theorem markedGroup_separable_and_not_isQuasidiagonalTrace :
    TopologicalSpace.SeparableSpace (ReducedGroupCStar MarkedGroup)
      ∧ ¬ Quasidiagonal.IsQuasidiagonalTrace
        (fun T : ReducedGroupCStar MarkedGroup ↦
          ReducedGroupCStarTrace.canonicalFaithfulTracialState MarkedGroup T) :=
  ⟨ReducedGroupCStarTrace.reducedGroupCStar_separableSpace MarkedGroup,
    markedGroup_canonicalReducedTrace_not_isQuasidiagonalTrace_unconditional⟩

/-- **The second route to `RE.05`, over one input fewer.**  Granting
Tikuisis--White--Winter and the UCT for this one algebra --- and nothing else
--- the reduced C⋆-algebra of the marked group is not nuclear. -/
theorem markedGroup_reducedGroupCStar_not_isNuclear_of_twwInput
    {UCT : Type → Prop} (tww : QuasidiagonalMF.TikuisisWhiteWinterInput UCT)
    (huct : UCT (ReducedGroupCStar MarkedGroup)) :
    ¬ CStarExactness.IsNuclearCStarAlgebra (ReducedGroupCStar MarkedGroup) :=
  markedGroup_reducedGroupCStar_not_isNuclear_of_tww
    Quasidiagonal.ucpContractive tww huct

end

end TikuisisWhiteWinterSites
end GroupApproximation
