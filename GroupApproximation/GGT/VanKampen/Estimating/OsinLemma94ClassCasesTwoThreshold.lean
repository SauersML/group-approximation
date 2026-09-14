import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassSectionTwoThreshold
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassPairTransfer
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassCornerMove
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4 on class words at two thresholds: the gap endpoints drop out

Osin (math/0411039v3, §9), proof of Lemma 9.4, Cases 1 and 2.  A backwards class-word pair with
connectors below `ε − B` and segments above `ε + B`, where `B = ⌈(c + 2) / λ⌉₊` bounds the gaps, gives a
backwards pair at `ε` with no endpoint strictly inside a gap: each such endpoint moves to its nearer
corner (`OsinLemma94ClassPolygons.exists_cornerPair_of_twoThreshold`).  That pair is single-side, and
the side-level Cases 1 and 2 refute it (`exists_sidePair_of_singleSide`), or it spans or splits across a
gap, the residual `OsinLemma94ClassCaseGapSpanStatement`.

Corner moves do not make a spanning pair single-side: a class can consist of many short sides between
hair gaps, and a source running across a gap has distance up to about the sum of its side parts.

* `osinLemma94ClassCasesTwoThreshold_of_residuals`: `OsinLemma94ClassCasesTwoThresholdInput` from the
  side-level Cases 1 and 2 and the spanning shape.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.4 inside the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **Cases 1 and 2 of Lemma 9.4 on class words at two thresholds**, from the side-level cases and the
spanning shape.  The gap endpoints are moved to corners first. -/
theorem osinLemma94ClassCasesTwoThreshold_of_residuals
    (hone : OsinLemma94CaseOneInput.{u, w, v}) (htwo : OsinLemma94CaseTwoInput.{u, w, v})
    (hspan : OsinLemma94ClassCaseGapSpanStatement.{u, w, v}) :
    OsinLemma94ClassCasesTwoThresholdInput.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e1, hone1⟩ := hone D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e2, htwo1⟩ := htwo D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨e4, hspan1⟩ := hspan D hhyper lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨max e1 (max e2 e4), fun eps heps => ?_⟩
  simp only [max_le_iff] at heps
  obtain ⟨he1, he2, he4⟩ := heps
  obtain ⟨r1, hr1, hone2⟩ := hone1 eps he1
  obtain ⟨r2, _, htwo2⟩ := htwo1 eps he2
  obtain ⟨r4, _, hspan2⟩ := hspan1 eps he4
  refine ⟨max r1 (max r2 r4), lt_of_lt_of_le hr1 (le_max_left _ _), fun rho hrho => ?_⟩
  simp only [max_le_iff] at hrho
  obtain ⟨hq1, hq2, hq4⟩ := hrho
  intro W hW Delta cuts hleast hcells hbelow S hcard hmin P hmax Q k C hlongS hlongT hback
  obtain ⟨C', hback', hnogap, -, -⟩ :=
    Q.exists_cornerPair_of_twoThreshold hlambda k C hlongS hlongT hback
  by_cases hsingle : Q.SingleSidePair k C'
  · obtain ⟨C'', hback''⟩ := Q.exists_sidePair_of_singleSide k C' hsingle
    by_cases hcut : P.kind k C''.target = .cutting
    · exact htwo2 rho hq2 W hW Delta cuts hleast hcells S hcard hmin P hmax k C''
        (hback'' hback') hcut
    · exact hone2 rho hq1 W hW Delta cuts hleast hcells hbelow S hcard hmin P hmax k C''
        (hback'' hback') hcut
  · exact hspan2 rho hq4 W hW Delta cuts hleast hcells hbelow S hcard hmin P hmax Q k C' hback'
      hnogap hsingle

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94ClassCasesTwoThreshold_of_residuals
