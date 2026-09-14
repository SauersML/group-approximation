import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellEnclosedSucc
import GroupApproximation.GGT.VanKampen.Estimating.OsinEnclosedLoopPocketUnpinch
import GroupApproximation.Meta.AxiomGuard

/-!
# Binder 3 over the successor-form loop cut at relator words longer than one letter

`OsinLemma94SameCellEnclosedSucc` proves binder 3 (`OsinLemma94CaseOneSameCellStatement`) over
`EnclosedSubdiagramLoopCutSuccStatement`.  The loop cut is proved at relator words longer than one
letter (`EnclosedSubdiagramLoopCutSuccLongStatement`, `OsinEnclosedSubdiagramLoopCutSuccProof`),
since the landed pinch doubles an edge at every bad corner.  Binder 3's consumers choose their own
threshold for `ρ`.  At `ρ ≥ 2` Osin's condition makes every relator word longer than one letter
(`one_lt_length_of_two_le_rho`), so the consumers take the restricted loop cut at the threshold
`max 2 ρ₁`.  This module is additive.

* `osinLemma94CaseOneNoSpurXPocket_of_enclosedLoopCutSuccLong`, `…NoSpurYPocket…`: the spur-free
  pockets.
* `osinLemma94CaseOneRCellSpur_of_enclosureLong`: the spur branch.
* `osinLemma94CaseOneSameCell_of_enclosedLoopCutSuccLong`: binder 3 over the restricted loop cut.
* `osinLemma94CaseOneSameCell_of_sideArcDoubling`: binder 3 over
  `EnclosedBridgeDoublingSideArcSuccStatement` alone, through `enclosedLoopPocketUnpinchSucc`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.HullSC
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.CaseOneWalk

open SameCellSimplePocket in
/-- **The spur-free X-pocket, refuted by the restricted successor-form loop cut**, at the threshold
`max 2 ρ₁`. -/
theorem osinLemma94CaseOneNoSpurXPocket_of_enclosedLoopCutSuccLong
    (hloop : EnclosedSubdiagramLoopCutSuccLongStatement.{u, w, v}) :
    OsinLemma94CaseOneXPocketStatementOf.{u, w, v}
      (fun Delta x b => ¬ PocketWalkSpurShape Delta x b) := by
  intro G _ Lambda D _hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨0, fun eps _ => ?_⟩
  obtain ⟨rho1, hrho1⟩ := exists_rho_large lambda c hmu eps
  refine ⟨max 2 rho1, by omega, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast _hpos hbelow S _hcard _hmin P _hmax k C _hback _hcut _hkind j
    sourceArc targetArc X Y r _hj htrav hs ht _hsource _htarget hX _hY n B A hPi hXB hout hsp
  have hlong := one_lt_length_of_two_le_rho hW (le_of_max_le_left hrho)
  have hne : X ++ B ≠ [] := by
    intro hnil
    apply hXB
    rw [hnil]
    rfl
  obtain ⟨hw, hfollows, heuler⟩ := SameCellPocketNoncrossing.pocketInputs_X (P.face_not_cell k j)
    sourceArc targetArc htrav hPi hs ht hne (fun d hd had => hsp ⟨d, hd, had⟩)
  have hencl := enclosedFaceSetSuccOfNoncrossing hw hout hfollows
  have hval : RelLetter.listVal
      (dartWord S.diagram (invDarts S.diagram X ++ invDarts S.diagram B)) ≠ 1 := by
    intro hone
    apply hXB
    have hinvd : invDarts S.diagram X ++ invDarts S.diagram B = invDarts S.diagram (B ++ X) := by
      simp only [invDarts, List.reverse_append, List.map_append]
    rw [hinvd, listVal_dartWord_invDarts, inv_eq_one, dartWord_append,
      RelWord.listVal_append] at hone
    rw [dartWord_append, RelWord.listVal_append]
    exact mul_eq_one_comm.mp hone
  obtain ⟨C₀, hC₀, hCf⟩ : ∃ C ∈ S.diagram.relatorCells, C.face ∈
      sideFaces S.diagram.toCombMap (invDarts S.diagram X ++ invDarts S.diagram B) := by
    by_contra hno
    apply hval
    have hcells : ∀ C ∈ S.diagram.relatorCells, C.face ∉
        (PocketRegion.ofNoncrossingClosedWalk hw hout hfollows heuler).faces :=
      fun C hC hmem => hno ⟨C, hC, hmem⟩
    rw [← PocketRegion.ofNoncrossingClosedWalk_invDarts_outer hw hout hfollows heuler,
      listVal_dartWord_invDarts,
      (PocketRegion.ofNoncrossingClosedWalk hw hout hfollows heuler).listVal_outer_eq_one hcells,
      inv_one]
  have hsides := SameCellPocketSides.face_not_mem_sideFaces_X (P.face_not_cell k j) sourceArc
    targetArc htrav hPi hs hw
  obtain ⟨Barc, hBarc⟩ : ∃ arc : CyclicArc (cellDarts S.diagram j), arc.darts = B := by
    have hrot : (cellDarts S.diagram j).rotate (n + targetArc.darts.length) =
        B ++ (sourceArc.darts ++ A ++ targetArc.darts) := by
      rw [← List.rotate_rotate, hPi]
      simp only [List.append_assoc]
      rw [List.rotate_append_length_eq]
      simp only [List.append_assoc]
    exact CyclicArc.exists_darts_eq_of_rotate_eq hrot
  have hnorm : WordMetric.wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord S.diagram (invDarts S.diagram X))) ≤ eps := by
    rw [listVal_dartWord_invDarts, WordMetric.wordNorm_inv D.alphabet.symmetricGenerating]
    exact (wordNorm_lt_of_end_connector C hX).le
  have hdecomposition : invDarts S.diagram
      (invDarts S.diagram (invDarts S.diagram X ++ invDarts S.diagram B)) =
        invDarts S.diagram X ++ invDarts S.diagram Barc.darts := by
    rw [hBarc]
    show ((invDarts S.diagram X ++ invDarts S.diagram B).reverse.map
      S.diagram.toCombMap.alpha).reverse.map S.diagram.toCombMap.alpha = _
    simp only [List.map_reverse, List.reverse_reverse, List.map_map,
      S.diagram.toCombMap.alpha_involutive.comp_self, List.map_id]
  obtain ⟨cut⟩ := hloop D eps rho mu lambda c hW hlambda1 hc hlong Delta S.diagram hleast S.equiv
    S.label_admissible _ _ hencl C₀ hC₀ hCf j hsides.2 Barc (invDarts S.diagram X)
    hdecomposition hnorm
  exact cut.false_of_below o52LeastArea hW hlambda hmu hmu1 (by omega)
    (hrho1 rho (le_of_max_le_right hrho)) hleast
    (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos cut.rCellCount_lt)

/-- **The spur-free Y-pocket, refuted by the restricted successor-form loop cut**, through the swap
of the connector pair. -/
theorem osinLemma94CaseOneNoSpurYPocket_of_enclosedLoopCutSuccLong
    (hloop : EnclosedSubdiagramLoopCutSuccLongStatement.{u, w, v}) :
    OsinLemma94CaseOneYPocketStatementOf.{u, w, v}
      (fun Delta x b => ¬ PocketWalkSpurShape Delta x b) :=
  osinLemma94CaseOneYPocketOf_of_xPocketOf (fun Delta x b => ¬ PocketWalkSpurShape Delta x b)
    (osinLemma94CaseOneNoSpurXPocket_of_enclosedLoopCutSuccLong hloop)

open SameCellRCellEnclosed SameCellSpurEnclosure in
/-- **The spur branch from the restricted enclosed loop cut**, at the threshold `max 2 ρ₁`. -/
theorem osinLemma94CaseOneRCellSpur_of_enclosureLong
    (hloop : EnclosedSubdiagramLoopCutSuccLongStatement.{u, w, v})
    (hsub : ClosedWalkEnclosedSubdiagramSuccStatement.{u, w, v})
    (hencl : OsinLemma94CaseOneSpurEnclosureStatement.{u, w, v}) :
    OsinLemma94CaseOneRCellSpurStatement.{u, w, v} := by
  intro G _ Lambda D _hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨0, fun eps _ => ?_⟩
  obtain ⟨rho1, hrho1⟩ := SameCellSimplePocket.exists_rho_large lambda c hmu eps
  refine ⟨max 2 rho1, by omega, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast _hpos hbelow S _hcard _hmin P _hmax k C _hback _hcut _hkind j
    sourceArc targetArc X Y r _hj htrav hs ht _hsource _htarget hX hY n B A hPi hXB hYA hsp
  have hlarge := hrho1 rho (le_of_max_le_right hrho)
  have hrho0 : 0 < rho := by omega
  have hlong := one_lt_length_of_two_le_rho hW (le_of_max_le_left hrho)
  rcases hencl S.diagram (P.face_ne_outer k) (P.face_not_cell k j) sourceArc targetArc htrav hPi
      hs ht (SameCellRCellAssembly.append_ne_nil_of_listVal_ne_one hXB)
      (SameCellRCellAssembly.append_ne_nil_of_listVal_ne_one hYA) hsp with
    ⟨F, hF, hcellOut⟩ | ⟨F, hF, hcellOut⟩
  · obtain ⟨C₀, hC₀, hCf⟩ : ∃ C ∈ S.diagram.relatorCells, C.face ∈ F := by
      by_contra hno
      exact listVal_invDarts_append_ne_one hXB
        (listVal_eq_one_of_enclosedSucc hsub hF fun C hC hmem => hno ⟨C, hC, hmem⟩)
    obtain ⟨Barc, hBarc⟩ : ∃ arc : CyclicArc (cellDarts S.diagram j), arc.darts = B := by
      have hrot : (cellDarts S.diagram j).rotate (n + targetArc.darts.length) =
          B ++ (sourceArc.darts ++ A ++ targetArc.darts) := by
        rw [← List.rotate_rotate, hPi]
        simp only [List.append_assoc]
        rw [List.rotate_append_length_eq]
        simp only [List.append_assoc]
      exact CyclicArc.exists_darts_eq_of_rotate_eq hrot
    have hnorm : WordMetric.wordNorm D.alphabet.carrier
        (RelLetter.listVal (dartWord S.diagram (invDarts S.diagram X))) ≤ eps := by
      rw [listVal_dartWord_invDarts, WordMetric.wordNorm_inv D.alphabet.symmetricGenerating]
      exact (wordNorm_lt_of_end_connector C hX).le
    have hdecomposition : invDarts S.diagram (B ++ X) =
        invDarts S.diagram X ++ invDarts S.diagram Barc.darts := by
      rw [hBarc]
      simp only [invDarts, List.reverse_append, List.map_append]
    obtain ⟨cut⟩ := hloop D eps rho mu lambda c hW hlambda1 hc hlong Delta S.diagram hleast
      S.equiv S.label_admissible F (B ++ X) hF C₀ hC₀ hCf j hcellOut Barc (invDarts S.diagram X)
      hdecomposition hnorm
    exact cut.false_of_below o52LeastArea hW hlambda hmu hmu1 hrho0 hlarge hleast
      (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos cut.rCellCount_lt)
  · obtain ⟨C₀, hC₀, hCf⟩ : ∃ C ∈ S.diagram.relatorCells, C.face ∈ F := by
      by_contra hno
      exact listVal_invDarts_append_ne_one hYA
        (listVal_eq_one_of_enclosedSucc hsub hF fun C hC hmem => hno ⟨C, hC, hmem⟩)
    obtain ⟨Aarc, hAarc⟩ : ∃ arc : CyclicArc (cellDarts S.diagram j), arc.darts = A := by
      have hrot : (cellDarts S.diagram j).rotate
          (n + (targetArc.darts ++ B ++ sourceArc.darts).length) =
            A ++ (targetArc.darts ++ B ++ sourceArc.darts) := by
        rw [← List.rotate_rotate, hPi, List.rotate_append_length_eq]
      exact CyclicArc.exists_darts_eq_of_rotate_eq hrot
    have hnorm : WordMetric.wordNorm D.alphabet.carrier
        (RelLetter.listVal (dartWord S.diagram (invDarts S.diagram Y))) ≤ eps := by
      rw [listVal_dartWord_invDarts, WordMetric.wordNorm_inv D.alphabet.symmetricGenerating]
      exact (wordNorm_lt_of_start_connector C hY).le
    have hdecomposition : invDarts S.diagram (A ++ Y) =
        invDarts S.diagram Y ++ invDarts S.diagram Aarc.darts := by
      rw [hAarc]
      simp only [invDarts, List.reverse_append, List.map_append]
    obtain ⟨cut⟩ := hloop D eps rho mu lambda c hW hlambda1 hc hlong Delta S.diagram hleast
      S.equiv S.label_admissible F (A ++ Y) hF C₀ hC₀ hCf j hcellOut Aarc (invDarts S.diagram Y)
      hdecomposition hnorm
    exact cut.false_of_below o52LeastArea hW hlambda hmu hmu1 hrho0 hlarge hleast
      (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos cut.rCellCount_lt)

/-- **Binder 3 over the restricted successor-form loop cut**, with the enclosed subdiagram and the
spur enclosure closed. -/
theorem osinLemma94CaseOneSameCell_of_enclosedLoopCutSuccLong
    (hloop : EnclosedSubdiagramLoopCutSuccLongStatement.{u, w, v}) :
    OsinLemma94CaseOneSameCellStatement.{u, w, v} :=
  osinLemma94CaseOneSameCell_of_noSpurPockets
    (osinLemma94CaseOneNoSpurXPocket_of_enclosedLoopCutSuccLong hloop)
    (osinLemma94CaseOneNoSpurYPocket_of_enclosedLoopCutSuccLong hloop)
    (osinLemma94CaseOneRCellSpur_of_enclosureLong hloop closedWalkEnclosedSubdiagramSucc
      osinLemma94CaseOneSpurEnclosure)

/-- **Binder 3 over the side-and-arc doubling alone**, through the closed unpinch, collar insertion
and cell transport. -/
theorem osinLemma94CaseOneSameCell_of_sideArcDoubling
    (hdouble : EnclosedBridgeDoublingSideArcSuccStatement.{u, w, v}) :
    OsinLemma94CaseOneSameCellStatement.{u, w, v} :=
  osinLemma94CaseOneSameCell_of_enclosedLoopCutSuccLong
    (enclosedSubdiagramLoopCutSuccLong_of_doubling hdouble)

end GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen

#audit_axioms osinLemma94CaseOneNoSpurXPocket_of_enclosedLoopCutSuccLong
#audit_axioms osinLemma94CaseOneNoSpurYPocket_of_enclosedLoopCutSuccLong
#audit_axioms osinLemma94CaseOneRCellSpur_of_enclosureLong
#audit_axioms osinLemma94CaseOneSameCell_of_enclosedLoopCutSuccLong
#audit_axioms osinLemma94CaseOneSameCell_of_sideArcDoubling
