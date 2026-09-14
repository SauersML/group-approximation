import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketPinch
import GroupApproximation.GGT.VanKampen.Estimating.OsinEnclosedSubdiagramLoopCut
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketNoncrossing
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellSimplePocket
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionNoncrossingWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94OneCellValue
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52LeastArea
import GroupApproximation.Meta.AxiomGuard

/-!
# The X-pocket of Lemma 9.4, Case 1, through the enclosed subdiagram

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, across one relator cell `Π`, relator-cell branch.
The loop cut on origin before this module takes pocket regions whose two cycles follow their
boundary walks (ruling R1), so only simple pocket walks.  A pocket walk that repeats a vertex (a
face bubble, a cell pinch, a touch between the face and the cell) is noncrossing but not simple,
and its complement cycle follows while its pocket cycle need not.  The loop cut from an enclosed
subdiagram (`EnclosedSubdiagramLoopCutStatement`) needs no following condition, so it takes all of
these walks at once.

* When the exterior face is off the side of `invDarts X ++ invDarts B`, no dart of the walk meets its
  reverse (the spur shape) or `OsinLemma94CaseOneSpurStatement` applies.
* Without a spur the walk is noncrossing, and its complement cycle follows its boundary walk
  (`SameCellPocketNoncrossing.pocketInputs_X`).
* `EnclosedFaceSetOfNoncrossingStatement`: a noncrossing walk whose complement cycle follows its
  boundary walk encloses the faces on its side, with the reversed walk as outside walk.
* The walk reads an element other than `1`, so the pocket holds a relator cell
  (`PocketRegion.listVal_outer_eq_one` on `PocketRegion.ofNoncrossingClosedWalk`).
* `Π` is off the side (`SameCellPocketSides.face_not_mem_sideFaces_X`), `B` is an arc of its
  carrier, and the side `invDarts X` has word norm less than `ε`.
* The enclosed loop cut and `OsinLoopCut.false_of_below` finish.

`osinLemma94CaseOneXPocket_of_enclosed` proves the X-pocket statement from the enclosed loop cut,
the enclosed face set of a noncrossing walk and the spur statement.  It replaces the five shape
statements of `OsinLemma94SameCellPocketPinch` and the walk-level shapes of
`OsinLemma94SameCellPocketIsland`, except the spur.

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

/-- **A noncrossing walk encloses the faces on its side.**  If a noncrossing closed walk has the
exterior face off its side and its complement cycle follows its boundary walk, the faces on its
side form an enclosed face set with the reversed walk as outside walk. -/
def EnclosedFaceSetOfNoncrossingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (walk : List Delta.toCombMap.Dart)
    (hw : IsNoncrossingClosedWalk Delta.toCombMap walk),
    Delta.outerFace ∉ sideFaces Delta.toCombMap walk →
    (hw.outerCycle Delta.planar).FollowsBoundary →
    EnclosedFaceSet Delta (sideFaces Delta.toCombMap walk) (invDarts Delta walk)

open SameCellSimplePocket in
/-- **The X-pocket from the enclosed loop cut.** -/
theorem osinLemma94CaseOneXPocket_of_enclosed
    (hloop : EnclosedSubdiagramLoopCutStatement.{u, w, v})
    (hface : EnclosedFaceSetOfNoncrossingStatement.{u, w, v})
    (hspur : OsinLemma94CaseOneSpurStatement.{u, w, v}) :
    OsinLemma94CaseOneXPocketStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨e5, he5⟩ := hspur D hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨e5, fun eps heps => ?_⟩
  obtain ⟨r5, hr5, h5⟩ := he5 eps heps
  obtain ⟨rho1, hrho1⟩ := exists_rho_large lambda c hmu eps
  refine ⟨max r5 (max 1 rho1), by omega, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax k C hback hcut hkind j sourceArc
    targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A hPi hXB hout _
  by_cases hsp : PocketWalkSpurShape S.diagram (invDarts S.diagram X) (invDarts S.diagram B)
  · exact h5 rho (le_of_max_le_left hrho) W hW Delta cuts hleast hpos hbelow S hcard hmin P hmax
      k C hback hcut hkind j sourceArc targetArc X Y r hj htrav hs ht hsource htarget hX hY n B A
      hPi hXB hout hsp
  have hne : X ++ B ≠ [] := by
    intro hnil
    apply hXB
    rw [hnil]
    rfl
  obtain ⟨hw, hfollows, heuler⟩ := SameCellPocketNoncrossing.pocketInputs_X (P.face_not_cell k j)
    sourceArc targetArc htrav hPi hs ht hne (fun d hd had => hsp ⟨d, hd, had⟩)
  have hencl := hface S.diagram _ hw hout hfollows
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
    (hrho1 rho (le_of_max_le_right (le_of_max_le_right hrho))) hleast
    (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos cut.rCellCount_lt)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneXPocket_of_enclosed
