import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.DiffKind
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassSameCell
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 04: GapSpan from the relator-cell branch

`OsinLemma94ClassCaseGapSpanStatement` follows from `OsinLemma94ClassCaseOneRCellStatement`. The
steps are those of `osinLemma94ClassCaseGapSpanSmall_of_residuals`, without the short-connector
hypotheses.

* The threshold is `ε₀ = max 3 (max ε₁ ε₂)`. Here `ε₁` is the Morse threshold, and `ε₂` and `ρ₀`
  come from the relator-cell branch.
* **Cutting targets.** `osinLemma94ClassCaseTwo_false`.
* **Equal kinds.** The face walk of `exists_sameCellWalk`. Then either the value-one kills, or the
  relator-cell branch.
* **Different kinds.** `false_of_diffKind` (module `Piece04.DiffKind`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.VanKampen.CaseOneWalk

/-- **GapSpan from the relator-cell branch.** -/
theorem gapSpan_of_rCell (hrcell : OsinLemma94ClassCaseOneRCellStatement.{u, w, v}) :
    OsinLemma94ClassCaseGapSpanStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨kappa, hmorse, eps1, heps1⟩ :=
    exists_morse_threshold_of_fourPoint D hhyper lambda c hlambda
  obtain ⟨eps2, heps2⟩ := hrcell D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨max 3 (max eps1 eps2), fun eps heps => ?_⟩
  have h3 : 3 ≤ eps := le_of_max_le_left heps
  have h1 : eps1 ≤ eps := le_of_max_le_left (le_of_max_le_right heps)
  have h2 : eps2 ≤ eps := le_of_max_le_right (le_of_max_le_right heps)
  obtain ⟨rho2, hrho2, hrho2'⟩ := heps2 eps h2
  refine ⟨rho2, hrho2, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax Q k C hback hnogap hnotsingle
  by_cases hcut : Q.classKind k C.target = .cutting
  · exact osinLemma94ClassCaseTwo_false
      GloballyDistinguishedSectionFamily.separatedCornerInsertionInput h3 hmin P Q k C hback hcut
      hnogap
  by_cases hkind : Q.classKind k C.source = Q.classKind k C.target
  · obtain ⟨j, sourceArc, targetArc, X, Y, r, hj, htrav, hsw, htw, -, -, hsource, htarget, hX, hY⟩ :=
      Q.exists_sameCellWalk k C hback hkind hnogap
    have hthreshold := heps1 eps h1
    refine hrho2' rho hrho W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax Q k C hback
      hnogap hnotsingle j sourceArc targetArc X Y r hj (hkind.symm.trans hj) htrav hsw htw hX hY ?_
    intro n B A hPi
    refine ⟨fun hXB => ?_, fun hYA => ?_⟩
    · obtain ⟨T, hT⟩ := CyclicArc.exists_darts_eq_of_rotate_eq hPi
      exact false_of_classSameCell_value_one_X hW hlambda.le hmorse hthreshold C sourceArc
        targetArc hsource htarget hX T hT hXB
    · obtain ⟨T, hT⟩ := CaseOneSameCell.exists_arc_darts_eq_rotate_four hPi
      exact false_of_classSameCell_value_one_Y hW hlambda.le hmorse hthreshold C sourceArc
        targetArc hsource htarget hY T hT hYA
  exact false_of_diffKind Q h3 k C hback hnogap hcut hkind

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.gapSpan_of_rCell
