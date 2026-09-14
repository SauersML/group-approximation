import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketIsland
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellSimplePocket
import GroupApproximation.Meta.AxiomGuard

/-!
# The X-pocket of Lemma 9.4, Case 1, at walk level, with a simple walk

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, across one relator cell `Π`, relator-cell branch.
`OsinLemma94SameCellPocketIsland` states the X-pocket over walks `s ++ invDarts B`, where `s` is a
sublist of `invDarts X` with the value of `invDarts X`.  This module closes the case where that walk
is simple, `OsinLemma94CaseOneWalkSimpleStatement`, through the walk-level loop-cut kill
`SameCellSimplePocket.false_of_simpleWalk_of_below`.

* The walk is simple: closed by hypothesis, with no repeated vertex and no dart met with its reverse
  by the shape.
* `B` is an arc of the carrier of `Π`, and the walk decomposes as `s ++ invDarts B`.
* The side `s` reads the value of `invDarts X`, of word norm less than `ε`
  (`wordNorm_lt_of_end_connector`).
* `Π` is off the side (`SameCellWalkSimple.face_not_mem_sideFaces_sublist`).  Every dart of the walk
  reverses a dart of `X`, on the polygon face, or of `B`, on `Π`, and the first dart of `p` joins
  the two faces off the walk.
* The walk reads an element other than `1`, since `X B` does.

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

namespace SameCellWalkSimple

/-- **`f` and `Π` off the side of a pocket walk through a sublist of `invDarts X`.**  The
walk-level form of `SameCellPocketSides.face_not_mem_sideFaces_X`. -/
theorem face_not_mem_sideFaces_sublist {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
    {f : Delta.toCombMap.Face} {j : Fin Delta.rCellCount} (hf : (cell Delta j).face ≠ f)
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {X Y : List Delta.toCombMap.Dart}
    {r : ℕ} (htrav : (Delta.faceBoundary f).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    {B A : List Delta.toCombMap.Dart} {n : ℕ}
    (hPi : (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    (hs : 0 < sourceArc.length) {s : List Delta.toCombMap.Dart}
    (hsub : s.Sublist (invDarts Delta X))
    (hw : IsNoncrossingClosedWalk Delta.toCombMap (s ++ invDarts Delta B)) :
    f ∉ sideFaces Delta.toCombMap (s ++ invDarts Delta B) ∧
      (cell Delta j).face ∉ sideFaces Delta.toCombMap (s ++ invDarts Delta B) := by
  obtain ⟨e, he₁, he₂, heB, -, heX, -⟩ :=
    SameCellPocketSides.exists_edge sourceArc targetArc htrav hPi hs
  have hX : ∀ z ∈ X, Delta.toCombMap.faceOf z = f := fun z hz =>
    SameCellPocketSides.faceOf_of_mem_rotate htrav
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hz)))
  have hB : ∀ z ∈ B, Delta.toCombMap.faceOf z = (cell Delta j).face := fun z hz =>
    SameCellPocketSides.faceOf_of_mem_cellDarts_rotate hPi
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hz)))
  have hmem : ∀ d ∈ s ++ invDarts Delta B,
      Delta.toCombMap.alpha d ∈ X ∨ Delta.toCombMap.alpha d ∈ B := by
    intro d hd
    rcases List.mem_append.mp hd with h | h
    · exact Or.inl (SameCellPocketSides.alpha_mem_of_mem_invDarts (hsub.subset h))
    · exact Or.inr (SameCellPocketSides.alpha_mem_of_mem_invDarts h)
  exact not_mem_sideFaces_of_two_faces Delta.planar hw
    (faceOf_alpha_eq_or_of_alpha_mem hX hB hmem) he₁ he₂
    (not_walkKeep_of_alpha_mem (Ne.symm hf) hX hB hmem he₁ he₂ heB heX)

end SameCellWalkSimple

open SameCellSimplePocket SameCellWalkSimple in
/-- **The X-pocket at walk level with a simple walk**, closed. -/
theorem osinLemma94CaseOneWalkSimple : OsinLemma94CaseOneWalkSimpleStatement.{u, w, v} := by
  intro G _ Lambda D _hhyper lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨0, fun eps _ => ?_⟩
  obtain ⟨rho1, hrho1⟩ := exists_rho_large lambda c hmu eps
  refine ⟨max 1 rho1, by omega, fun rho hrho => ?_⟩
  intro W hW Delta cuts hleast _hpos hbelow S _hcard _hmin P _hmax k C _hback _hcut _hkind j
    sourceArc targetArc X Y r _hj htrav hs _ht _hsource _htarget hX _hY n B A hPi hXB s hsub
    hclosed hval hout hshape
  obtain ⟨hne', hchain, hcloses⟩ := hclosed
  have hw : IsSimpleClosedWalk S.diagram.toCombMap (s ++ invDarts S.diagram B) :=
    ⟨hne', hchain, hcloses, hshape.1, hshape.2⟩
  obtain ⟨Barc, hBarc⟩ : ∃ arc : CyclicArc (cellDarts S.diagram j), arc.darts = B := by
    have hrot : (cellDarts S.diagram j).rotate (n + targetArc.darts.length) =
        B ++ (sourceArc.darts ++ A ++ targetArc.darts) := by
      rw [← List.rotate_rotate, hPi]
      simp only [List.append_assoc]
      rw [List.rotate_append_length_eq]
      simp only [List.append_assoc]
    exact CyclicArc.exists_darts_eq_of_rotate_eq hrot
  have hsides := face_not_mem_sideFaces_sublist (P.face_not_cell k j) sourceArc targetArc htrav
    hPi hs hsub hw.isNoncrossingClosedWalk
  have hnorm : WordMetric.wordNorm D.alphabet.carrier
      (RelLetter.listVal (dartWord S.diagram s)) ≤ eps := by
    rw [hval, listVal_dartWord_invDarts, WordMetric.wordNorm_inv D.alphabet.symmetricGenerating]
    exact (wordNorm_lt_of_end_connector C hX).le
  have hwalkval :
      RelLetter.listVal (dartWord S.diagram (s ++ invDarts S.diagram B)) ≠ 1 := by
    intro hone
    apply hXB
    rw [dartWord_append, RelWord.listVal_append, hval, ← RelWord.listVal_append,
      ← dartWord_append] at hone
    have hinvd : invDarts S.diagram X ++ invDarts S.diagram B = invDarts S.diagram (B ++ X) := by
      simp only [invDarts, List.reverse_append, List.map_append]
    rw [hinvd, listVal_dartWord_invDarts, inv_eq_one, dartWord_append,
      RelWord.listVal_append] at hone
    rw [dartWord_append, RelWord.listVal_append]
    exact mul_eq_one_comm.mp hone
  exact false_of_simpleWalk_of_below hW hlambda hlambda1 hc hmu hmu1 (by omega)
    (hrho1 rho (le_of_max_le_right hrho)) hleast hbelow S.equiv S.label_admissible hw hout
    hsides.2 Barc (by rw [hBarc]) hnorm hwalkval

end GroupApproximation.GGT.VanKampen

#audit_axioms
  GroupApproximation.GGT.VanKampen.SameCellWalkSimple.face_not_mem_sideFaces_sublist
#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneWalkSimple
