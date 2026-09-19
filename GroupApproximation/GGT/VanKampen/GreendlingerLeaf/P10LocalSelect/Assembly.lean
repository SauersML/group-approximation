import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.Statement
import GroupApproximation.Meta.AxiomGuard

/-!
# The quadrant move from the local selection (step 3)

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane ms-nm-uncond-b, step 3 of lane
nm-gl03d's plan.

`p10LS_quadrantMove_of_selection` proves `P10FilterMoveExists.p10FM_QuadrantMoveStatement` from
`p10LS_SelectionStatement`.  The selection statement is lane nm-gl03d's interface (`Statement`) and
is **OPEN** (step 2).  The proof takes the good lobe `B` from the selection and applies, case by case,
the matching proved witness lemma:

* a simple cyclic block with the rest of the cycle on its side: `p10QM_move_FF` when `o, s` are on
  the side, `p10QM_move_TF` when they are off it;
* a closed cyclic block with the rest off its side and both arcs off it: `p10QM_move_FT` when the
  kept face `k` is on the side, `p10QM_move_TT` otherwise;
* an untouched simple lobe with a rest dart on its side: `p10QS_move_untouched_FF` / `_TF`;
* an untouched simple lobe with a rest dart off its side: `p10QS_move_untouched_TT` / `_FT`.

These lemmas are from lanes gl-p10-92 and gl-p10-93 (P10QuadrantMove, P10QuadrantSelect).  Only
the dispatch is new here.  With `Full.GL03DQuadrant.relativeGreendlinger_of_allCells_of_quadrantMove`
this reads residual (ii) as the selection statement.

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams, residual 10).  It certifies
no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10FilterMoveExists
  P10QuadrantMove

/-- **The quadrant move from the local selection.**  `p10FM_QuadrantMoveStatement` from
`p10LS_SelectionStatement`, which is OPEN; each case of a good lobe is closed by its proved witness
lemma. -/
theorem p10LS_quadrantMove_of_selection (h : p10LS_SelectionStatement.{v}) :
    p10FM_QuadrantMoveStatement.{v} := by
  intro M F c o s k bs bo a b s₁ s₂ hM hc hpin hnf hcross ho hs hso hk ha hb hsplit
  obtain ⟨B, hB⟩ :=
    h M F c o s k bs bo a b s₁ s₂ hM hc hpin hnf hcross ho hs hso hk ha hb hsplit
  rcases hB with ⟨hblk, hBs, hP, hin, ⟨hoB, hsB⟩ | ⟨hoB, hsB⟩⟩ |
      ⟨hblk, hBw, hP, hout, hla, hlb⟩ |
      ⟨hBs, hBc, ⟨v0, hU⟩, hPin, ⟨hoB, hsB⟩ | ⟨hoB, hsB⟩⟩ |
      ⟨hBs, hBc, ⟨v0, hU⟩, hPout, ⟨hkB, hfa, hfb⟩ | ⟨hkB, hfa, hfb⟩⟩
  · exact p10QM_move_FF M F c o s k bs bo a b s₁ s₂ B hM hc hk hsplit hblk hBs hP hin hoB hsB
  · exact p10QM_move_TF M F c o s k bs bo a b s₁ s₂ B hM hk hsplit hblk hBs hP hin hoB hsB
  · by_cases hkB : k ∈ sideFaces M B
    · exact p10QM_move_FT M F c o s k bs bo a b s₁ s₂ B hsplit hblk hBw hP hout ho hs hkB
        hla hlb
    · exact p10QM_move_TT M F c o s k bs bo a b s₁ s₂ B hc hsplit hblk hBw hP hout ho hs hkB
        hla hlb
  · exact p10QS_move_untouched_FF M F c o s k bs bo a b s₁ s₂ B hM hc hk hsplit hBs hBc hU hPin
      hoB hsB
  · exact p10QS_move_untouched_TF M F c o s k bs bo a b s₁ s₂ B hM hc hk hsplit hBs hBc hU hPin
      hoB hsB
  · exact p10QS_move_untouched_TT M F c o s k bs bo a b B hM hc hBs hBc hU hPout ho hs hkB hfa hfb
  · exact p10QS_move_untouched_FT M F c o s k bs bo a b B hM hc hBs hBc hU hPout ho hs hkB hfa hfb

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10LocalSelect.p10LS_quadrantMove_of_selection
