import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedNoncrossing
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellYPocket
import GroupApproximation.Meta.AxiomGuard

/-!
# The spur-free X- and Y-pockets of Lemma 9.4, Case 1, from the enclosed loop cut

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, across one relator cell `Π`, relator-cell branch.
`OsinLemma94SameCellPocketEnclosed` refutes the X-pocket through the loop cut from an enclosed
subdiagram, over three inputs: that loop cut, the enclosed face set of a noncrossing walk, and the
spur statement.  The second input is now closed (`enclosedFaceSetOfNoncrossing`).  This module
states the pockets over the loop cut alone.

* `osinLemma94CaseOneNoSpurXPocket_of_enclosedLoopCut`: the X-pocket whose walk meets no dart
  together with its reverse is refuted by the enclosed loop cut.
* `osinLemma94CaseOneNoSpurYPocket_of_enclosedLoopCut`: the same for the Y-pocket, through the swap
  of the connector pair (`osinLemma94CaseOneYPocketOf_of_xPocketOf`).
* `osinLemma94CaseOneXPocket_of_enclosedLoopCut` and `osinLemma94CaseOneYPocket_of_enclosedLoopCut`:
  the pockets with no shape condition, over the loop cut and the spur statement.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1).  It certifies no printed sentence on its own.
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
/-- **The spur-free X-pocket, refuted by the enclosed loop cut.** -/
theorem osinLemma94CaseOneNoSpurXPocket_of_enclosedLoopCut
    (hloop : EnclosedSubdiagramLoopCutStatement.{u, w, v}) :
    OsinLemma94CaseOneXPocketStatementOf.{u, w, v}
      (fun Delta x b => ¬ PocketWalkSpurShape Delta x b) := by
  intro G _ Lambda D _hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨0, fun eps _ => ?_⟩
  obtain ⟨rho1, hrho1⟩ := exists_rho_large lambda c hmu eps
  refine ⟨max 1 rho1, by omega, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast _hpos hbelow S _hcard _hmin P _hmax k C _hback _hcut _hkind j
    sourceArc targetArc X Y r _hj htrav hs ht _hsource _htarget hX _hY n B A hPi hXB hout hsp
  have hne : X ++ B ≠ [] := by
    intro hnil
    apply hXB
    rw [hnil]
    rfl
  obtain ⟨hw, hfollows, heuler⟩ := SameCellPocketNoncrossing.pocketInputs_X (P.face_not_cell k j)
    sourceArc targetArc htrav hPi hs ht hne (fun d hd had => hsp ⟨d, hd, had⟩)
  have hencl := enclosedFaceSetOfNoncrossing S.diagram _ hw hout hfollows
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
  obtain ⟨cut⟩ := hloop D eps rho mu lambda c hW hlambda1 hc Delta S.diagram hleast S.equiv
    S.label_admissible _ _ hencl C₀ hC₀ hCf j hsides.2 Barc (invDarts S.diagram X)
    hdecomposition hnorm
  exact cut.false_of_below o52LeastArea hW hlambda hmu hmu1 (by omega)
    (hrho1 rho (le_of_max_le_right hrho)) hleast
    (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos cut.rCellCount_lt)

/-- **The spur-free Y-pocket, refuted by the enclosed loop cut**, through the swap of the connector
pair. -/
theorem osinLemma94CaseOneNoSpurYPocket_of_enclosedLoopCut
    (hloop : EnclosedSubdiagramLoopCutStatement.{u, w, v}) :
    OsinLemma94CaseOneYPocketStatementOf.{u, w, v}
      (fun Delta x b => ¬ PocketWalkSpurShape Delta x b) :=
  osinLemma94CaseOneYPocketOf_of_xPocketOf (fun Delta x b => ¬ PocketWalkSpurShape Delta x b)
    (osinLemma94CaseOneNoSpurXPocket_of_enclosedLoopCut hloop)

/-- **The X-pocket over the enclosed loop cut and the spur statement.** -/
theorem osinLemma94CaseOneXPocket_of_enclosedLoopCut
    (hloop : EnclosedSubdiagramLoopCutStatement.{u, w, v})
    (hspur : OsinLemma94CaseOneSpurStatement.{u, w, v}) :
    OsinLemma94CaseOneXPocketStatement.{u, w, v} :=
  osinLemma94CaseOneXPocket_of_enclosed hloop enclosedFaceSetOfNoncrossing hspur

/-- **The Y-pocket over the enclosed loop cut and the spur statement.** -/
theorem osinLemma94CaseOneYPocket_of_enclosedLoopCut
    (hloop : EnclosedSubdiagramLoopCutStatement.{u, w, v})
    (hspur : OsinLemma94CaseOneSpurStatement.{u, w, v}) :
    OsinLemma94CaseOneYPocketStatement.{u, w, v} :=
  osinLemma94CaseOneYPocketOf_of_xPocketOf (fun _ _ _ => True)
    (osinLemma94CaseOneXPocket_of_enclosedLoopCut hloop hspur)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneNoSpurXPocket_of_enclosedLoopCut
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneNoSpurYPocket_of_enclosedLoopCut
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneXPocket_of_enclosedLoopCut
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneYPocket_of_enclosedLoopCut
