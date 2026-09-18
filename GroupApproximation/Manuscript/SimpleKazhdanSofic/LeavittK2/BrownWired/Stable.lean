import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownWired.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.UsedRankFourCloseStable
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.Superperfect
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2Endpoints
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown wired III: the `K₂` gaps collapse onto superperfect units (lane sk-leavitt-29)

Let `L = L_{𝔽₂}(1,2)` and `hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement`.
With Brown's extension wired (`BrownWired/Criterion`), `hsp` gives `K₂(4, L) = ⊥`
(`binaryLeavittRankFourInjective_of_unitsSuperperfect`).  So every rank-four and rank-five `K₂`
statement in `LeavittK2` and `LeavittFP` follows from `hsp` alone:

* `K₂(5, L) = ⊥` (`LeavittFP.binaryLeavittSteinbergInjective_of_rankFour`);
* the used statements (lanes sk-leavitt-24/25) and stable `K₂(L) = 0` in finite-stage form
  (lane sk-leavitt-26);
* injective stability from rank five (`BinaryLeavittK2FiveStabilityStatement`).

The loop closes as well: `K₂(4, L) = ⊥ → K₂(5, L) = ⊥ → hsp`
(`superperfect_of_binaryLeavittSteinbergInjective`).  Hence
`binaryLeavittRankFourInjective_iff_unitsSuperperfect`.

## Remaining gap (LOUD)

`EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement` (`LeavittK2/EndpointInterfaces.lean:45`).
It is *equivalent* to `K₂(4, L) = ⊥` and to `K₂(5, L) = ⊥`, so it is not logically weaker than
those.  In proof content it is Khanh Thm 2.2 (`Lˣ` superperfect).

## Truth check

All statements are true (Khanh, arXiv:2609.08428, Thm 2.2 and Thm 5.4; Ara–Brustenga–Cortiñas).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift

/-- `K₂(5, L_{𝔽₂}(1,2)) = ⊥` from superperfect units alone. -/
theorem binaryLeavittSteinbergInjective_of_unitsSuperperfect
    (hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    LeavittFP.BinaryLeavittSteinbergInjectiveStatement :=
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.binaryLeavittSteinbergInjective_of_rankFour
    (binaryLeavittRankFourInjective_of_unitsSuperperfect hsp)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.binaryLeavittSteinbergInjective_of_unitsSuperperfect

/-- **The gap equivalence.**  With Brown wired, `K₂(4, L_{𝔽₂}(1,2)) = ⊥` iff `L_{𝔽₂}(1,2)ˣ` is
superperfect. -/
theorem binaryLeavittRankFourInjective_iff_unitsSuperperfect :
    LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement ↔
      EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement :=
  ⟨fun h =>
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.superperfect_of_binaryLeavittSteinbergInjective
      (GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.binaryLeavittSteinbergInjective_of_rankFour h),
    binaryLeavittRankFourInjective_of_unitsSuperperfect⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.binaryLeavittRankFourInjective_iff_unitsSuperperfect

/-- The rank-four used statement (lane sk-leavitt-25) from superperfect units alone. -/
theorem leavittK2UsedRankFour_of_unitsSuperperfect
    (hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.LeavittK2UsedRankFourStatement :=
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.leavittK2UsedRankFour_of_rankFourInjective
    (binaryLeavittRankFourInjective_of_unitsSuperperfect hsp)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.leavittK2UsedRankFour_of_unitsSuperperfect

/-- The rank-five used statement (lane sk-leavitt-24) from superperfect units alone. -/
theorem leavittK2Used_of_unitsSuperperfect
    (hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.LeavittK2UsedStatement :=
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.leavittK2Used_of_rankFour
    (leavittK2UsedRankFour_of_unitsSuperperfect hsp)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.leavittK2Used_of_unitsSuperperfect

/-- Stable `K₂(L_{𝔽₂}(1,2)) = 0` in finite-stage form, from superperfect units alone. -/
theorem binaryLeavittStableK2Trivial_of_unitsSuperperfect
    (hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BinaryLeavittStableK2TrivialStatement :=
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittStableK2Trivial_of_leavittK2UsedRankFour
    (leavittK2UsedRankFour_of_unitsSuperperfect hsp)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.binaryLeavittStableK2Trivial_of_unitsSuperperfect

/-- Injective stability for `K₂` from rank five, from superperfect units alone. -/
theorem binaryLeavittK2FiveStability_of_unitsSuperperfect
    (hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BinaryLeavittK2FiveStabilityStatement :=
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittK2FiveStability_of_binaryLeavittSteinbergInjective
    (binaryLeavittSteinbergInjective_of_unitsSuperperfect hsp)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.binaryLeavittK2FiveStability_of_unitsSuperperfect

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift
