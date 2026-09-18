import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyBelow
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkEulerSectorFree
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellKeptCell
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCellSection
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellSimplePocket
import GroupApproximation.GGT.VanKampen.Estimating.OsinEnclosedSubdiagramLoopCutSuccProof
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52Prep
import GroupApproximation.GGT.VanKampen.SurgeryOuterCellThickening
import GroupApproximation.Manuscript.NonMF.Full.GL03BPinch.Statement
import GroupApproximation.Manuscript.NonMF.Full.GL06g.Exit
import GroupApproximation.Manuscript.NonMF.Full.GL06e.TwoArcUnpinch
import GroupApproximation.Meta.AxiomGuard

/-!
# The lake exclusion from the enclosed inner pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

`proof_of_innerPocketEnclosed` derives the proper arcs of the cell pocket walk below the inductive
bound (`CellPocketWalkProperArcsBelowSectionStatement`) from the enclosed inner pocket
`GL03B.InnerPocketEnclosedTwoArcLocal`.  Beyond the thresholds `ρ ≥ max 2 ρ₁`:
* the pocket walk is a pocket region (`cellPocketWalkEuler`, `ofNoncrossingClosedWalkEuler`);
* it holds a kept relator cell off both candidates, whose value is not `1`
  (`exists_kept_of_cellPocketRegion_of_leastArea`, `leastArea_listVal_word_ne_one`);
* the enclosed inner pocket gives a two-arc face set, unpinched to a `TwoArcExit`
  (`GL06e.twoArcExit_of_enclosed`, using `one_lt_length_of_two_le_rho`);
* clause (b) below the relator count refutes the exit (`GL06g.false_of_twoArcExit`).

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06g

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded

/-- **The lake exclusion from the enclosed inner pocket** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121).  A cell pocket walk with the exterior off its side
and an arc not proper holds a kept relator cell off both candidates.  The enclosed inner pocket
around it unpinches to a pocket region with two arcs outside, which clause (b) below the relator
count refutes. -/
theorem proof_of_innerPocketEnclosed (h : GL03BPinch.InnerPocketEnclosedTwoArcCorrected.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D _ lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨0, fun eps _ => ?_⟩
  obtain ⟨rho1, hrho1⟩ := SameCellSimplePocket.exists_rho_large lambda c hmu eps
  refine ⟨max 2 rho1, by omega, fun rho hrho W hcondition => ?_⟩
  have hlarge := hrho1 rho (le_of_max_le_right hrho)
  have hrho2 : 2 ≤ rho := le_of_max_le_left hrho
  intro Delta _ hlea hbelow S i j a b ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw hoff
  exfalso
  have hlea' : S.diagram.LeastArea := OuterCellThickening.leastArea_of_oEquivalent S.equiv hlea
  obtain ⟨hinner, houter⟩ :=
    cellPocketWalkEuler hlea S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw
  obtain ⟨kept, hkept⟩ := S.exists_kept_of_cellPocketRegion_of_leastArea ha hb hab hij hai hbi K
    hfirst hsecond h₁ hlea' (PocketRegion.ofNoncrossingClosedWalkEuler hw hoff hinner houter) rfl
  rw [PocketRegion.ofNoncrossingClosedWalkEuler_faces] at hkept
  have hcell : ∀ z : RegionCandidate D eps S.diagram, (cell S.diagram kept).face ∉ z.1 := by
    intro z hkz
    have hz := (z.2.boundary.all_gCells _ hkz).2
    rw [DiscDiagram.faceWord, ← S.diagram.relatorCell_word _ (cell_mem S.diagram kept)] at hz
    exact DiscDiagram.leastArea_listVal_word_ne_one hlea' _ (cell_mem S.diagram kept) hz
  have hbelow' : OsinLemma97Below.{u, w, v} D lambda c mu eps W S.diagram.rCellCount := by
    rw [S.equiv.rCellCount_eq]
    exact hbelow
  have hW : ∀ word ∈ W, 1 < word.length := one_lt_length_of_two_le_rho hcondition hrho2
  rcases h D eps S.diagram a b K hij hai hbi (S.pairwise a ha b hb hab) S.label_admissible hW
      hfirst hsecond h₁ h₂ hw hoff hinner houter _ (cell_mem S.diagram kept) hkept (hcell a)
      (hcell b) with
    ⟨faces, outerWalk, k₁, k₂, A₁, A₂, s₁, s₂, E, hC, hk₁, hk₂, hdec, hs₁, hs₂, hpos⟩ | hall
  swap
  -- DRAFT GAP (not landable): the all-cells disjunct `hall`; refutation pending (WO sent to main).
  · exact ALLCELLS_REFUTATION_PENDING hall
  exact false_of_twoArcExit hcondition hlambda hlambda1 hc hmu hmu1 hrho2 hlarge hlea' hbelow'
    (GL06e.twoArcExit_of_enclosed D S.label_admissible hW E hC hk₁ hk₂ A₁ A₂ s₁ s₂ hdec hs₁ hs₂
      hpos)

end GroupApproximation.Full.GL06g

#audit_axioms GroupApproximation.Full.GL06g.proof_of_innerPocketEnclosed
