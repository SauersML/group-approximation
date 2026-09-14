import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedBridgeDoublingStep
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedPocketRegion
import GroupApproximation.GGT.VanKampen.Estimating.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# Doubling every bridge of an enclosed face set

`EnclosedBridgeDoublingSuccStatement` (`ClosedWalkEnclosedSubdiagramPieces`): a nonempty face set
enclosed by an outside walk turning to its successor has an O-equivalent copy of the diagram whose
enclosed walk uses no edge in both directions, with the same word and as many enclosed relator
cells.  `ClosedWalkEnclosedBridgeDoublingStep` doubles one bridge dart.  This module chooses the
side and runs the induction.

* `facePerm_eq_self_of_length_one`, `mem_pair_of_monogons`: if a bridge dart and its reverse both
  bound monogons, the map has no other darts, so no face is enclosed.
* `exists_bridge_side`: some bridge dart of the walk lies on a face with at least two darts.
* `exists_index_eq_dart`: its position on its face traversal.
* `cellCorrespondence_map`: a doubling keeps the relator cells in order, with their words, and
  a cell is enclosed exactly when its image is.
* `one_lt_faceBoundary_length_of_bridge`: under the successor form, every bridge dart lies on a face
  with at least two darts, so an enclosed face is not needed to choose the side.
* `DoublingOutput`, `doublingOutputSucc`: the induction on the number of bridge darts, with the cell
  correspondence, for any enclosed face set turning to its successor (the one-edge tree walk
  `[e, ē]` encloses no face).  `doublingOutput` is its first form, with an enclosed face.
* `enclosedBridgeDoublingSucc`: the statement.
* `enclosedLeastAreaFilterSucc`: the successor-form singular least-area filter, closed.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemmas 9.4 and 9.7); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Equiv SimpleClosedWalkSides EdgeInsertion Embedded

namespace EnclosedBridgeDoubling

/-- A dart on a face traversal of length one is fixed by the face permutation. -/
theorem facePerm_eq_self_of_length_one {M : CombMap.{v}} {f : M.Face} (B : FaceBoundary M f)
    (hlen : B.darts.length = 1) {d : M.Dart} (hd : d ∈ B.darts) : M.facePerm d = d := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  obtain rfl : i = 0 := by omega
  have hcl := B.closes
  rw [List.getLast_eq_getElem, List.head_eq_getElem] at hcl
  have h0 : B.darts.length - 1 = 0 := by omega
  simpa only [h0] using hcl

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **Two monogons across one edge fill the map.** -/
theorem mem_pair_of_monogons (Delta : DiscDiagram.{u, w, v} W) {d : Delta.toCombMap.Dart}
    (h1 : (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts.length = 1)
    (h2 : (Delta.faceBoundary (Delta.toCombMap.faceOf (Delta.toCombMap.alpha d))).darts.length = 1)
    (x : Delta.toCombMap.Dart) : x = d ∨ x = Delta.toCombMap.alpha d := by
  have hf1 : Delta.toCombMap.facePerm d = d :=
    facePerm_eq_self_of_length_one _ h1 (((Delta.faceBoundary _).mem_iff d).mpr rfl)
  have hf2 : Delta.toCombMap.facePerm (Delta.toCombMap.alpha d) = Delta.toCombMap.alpha d :=
    facePerm_eq_self_of_length_one _ h2 (((Delta.faceBoundary _).mem_iff _).mpr rfl)
  have hsig : ∀ y, Delta.toCombMap.sigma y =
      Delta.toCombMap.facePerm (Delta.toCombMap.alpha y) := by
    intro y
    show Delta.toCombMap.sigma y =
      (Delta.toCombMap.sigma * Delta.toCombMap.alpha) (Delta.toCombMap.alpha y)
    rw [Perm.mul_apply, Delta.toCombMap.alpha_involutive]
  have hsd : Delta.toCombMap.sigma d = Delta.toCombMap.alpha d := by rw [hsig, hf2]
  have hsad : Delta.toCombMap.sigma (Delta.toCombMap.alpha d) = d := by
    rw [hsig, Delta.toCombMap.alpha_involutive, hf1]
  have hstep : ∀ y z, Delta.toCombMap.Adjacent y z →
      ((y = d ∨ y = Delta.toCombMap.alpha d) ↔ (z = d ∨ z = Delta.toCombMap.alpha d)) := by
    intro y z hyz
    rcases hyz with rfl | rfl
    · constructor
      · rintro (rfl | rfl)
        · exact Or.inr rfl
        · exact Or.inl (Delta.toCombMap.alpha_involutive _)
      · rintro (h | h)
        · right
          rw [← h, Delta.toCombMap.alpha_involutive]
        · left
          exact Delta.toCombMap.alpha.injective h
    · constructor
      · rintro (rfl | rfl)
        · exact Or.inr hsd
        · exact Or.inl hsad
      · rintro (h | h)
        · right
          exact Delta.toCombMap.sigma.injective (h.trans hsad.symm)
        · left
          exact Delta.toCombMap.sigma.injective (h.trans hsd.symm)
  have hinv : ∀ y z, Relation.EqvGen Delta.toCombMap.Adjacent y z →
      ((y = d ∨ y = Delta.toCombMap.alpha d) ↔ (z = d ∨ z = Delta.toCombMap.alpha d)) := by
    intro y z h
    induction h with
    | rel a b hab => exact hstep a b hab
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  exact (hinv d x (Delta.planar.1 d x)).mp (Or.inl rfl)

/-- **Some bridge dart lies on a face with at least two darts**, when a face is enclosed. -/
theorem exists_bridge_side (Delta : DiscDiagram.{u, w, v} W)
    {faces : Finset Delta.toCombMap.Face} {outerWalk : List Delta.toCombMap.Dart}
    (E : EnclosedFaceSet Delta faces outerWalk) (hne : faces.Nonempty)
    {d : Delta.toCombMap.Dart} (hd : d ∈ outerWalk) (had : Delta.toCombMap.alpha d ∈ outerWalk) :
    ∃ e ∈ outerWalk, Delta.toCombMap.alpha e ∈ outerWalk ∧
      1 < (Delta.faceBoundary (Delta.toCombMap.faceOf e)).darts.length := by
  by_cases h1 : 1 < (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts.length
  · exact ⟨d, hd, had, h1⟩
  by_cases h2 :
      1 < (Delta.faceBoundary (Delta.toCombMap.faceOf (Delta.toCombMap.alpha d))).darts.length
  · exact ⟨Delta.toCombMap.alpha d, had, by rw [Delta.toCombMap.alpha_involutive]; exact hd, h2⟩
  exfalso
  have hpos : ∀ x : Delta.toCombMap.Dart,
      0 < (Delta.faceBoundary (Delta.toCombMap.faceOf x)).darts.length :=
    fun x => List.length_pos_iff.mpr (Delta.faceBoundary _).nonempty
  have hl1 : (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts.length = 1 := by
    have := hpos d
    omega
  have hl2 :
      (Delta.faceBoundary (Delta.toCombMap.faceOf (Delta.toCombMap.alpha d))).darts.length = 1 := by
    have := hpos (Delta.toCombMap.alpha d)
    omega
  obtain ⟨f, hf⟩ := hne
  obtain ⟨x, rfl⟩ := Quotient.mk''_surjective f
  change Delta.toCombMap.faceOf x ∈ faces at hf
  rcases mem_pair_of_monogons Delta hl1 hl2 x with rfl | rfl
  · exact ((E.mem_iff _).mp hd).1 hf
  · exact ((E.mem_iff _).mp had).1 hf

/-- The position of a dart on the traversal of its face. -/
theorem exists_index_eq_dart (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
    {e : Delta.toCombMap.Dart} (he : e ∈ (Delta.faceBoundary f).darts) :
    ∃ j : Fin (Delta.faceBoundary f).darts.length, FaceEdgeDoubling.dart Delta f j = e := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  exact ⟨⟨i, hi⟩, by rw [FaceEdgeDoubling.dart_eq_get, List.get_eq_getElem]⟩

/-- **The relator cells correspond across a doubling**, in order and with their words. -/
theorem cellCorrespondence_map {Delta Delta' : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face} {faces' : Finset Delta'.toCombMap.Face}
    (cellImage : RelatorCell Delta.toCombMap Delta.outerFace W →
      RelatorCell Delta'.toCombMap Delta'.outerFace W)
    (hcells : Delta'.relatorCells = Delta.relatorCells.map cellImage)
    (hword : ∀ C, (cellImage C).word = C.word)
    (hface : ∀ C, (cellImage C).face ∈ faces' ↔ C.face ∈ faces) :
    ∃ e : Fin Delta.rCellCount ≃ Fin Delta'.rCellCount, ∀ i,
      (cell Delta' (e i)).word = (cell Delta i).word ∧
        ((cell Delta' (e i)).face ∈ faces' ↔ (cell Delta i).face ∈ faces) := by
  have hlen : Delta.rCellCount = Delta'.rCellCount := by
    show Delta.relatorCells.length = Delta'.relatorCells.length
    rw [hcells, List.length_map]
  have hget : ∀ i : Fin Delta.rCellCount,
      cell Delta' (finCongr hlen i) = cellImage (cell Delta i) := by
    intro i
    have key : ∀ (l : List (RelatorCell Delta'.toCombMap Delta'.outerFace W)),
        l = Delta.relatorCells.map cellImage → ∀ (k : ℕ) (hk : k < l.length)
          (hk' : k < Delta.relatorCells.length), l[k] = cellImage Delta.relatorCells[k] := by
      intro l hl k hk hk'
      subst hl
      exact List.getElem_map ..
    exact key Delta'.relatorCells hcells i.val _ i.isLt
  refine ⟨finCongr hlen, fun i => ?_⟩
  rw [hget i]
  exact ⟨hword _, hface _⟩

open scoped Classical in
/-- **The doubling output**: an O-equivalent copy with a bridge-free enclosed face set turning to
its successor, reading the same word, with corresponding relator cells. -/
def DoublingOutput (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face)
    (outerWalk : List Delta.toCombMap.Dart) : Prop :=
  ∃ (Delta' : DiscDiagram.{u, w, v} W) (faces' : Finset Delta'.toCombMap.Face)
    (outerWalk' : List Delta'.toCombMap.Dart),
    Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
    EnclosedFaceSetSucc Delta' faces' outerWalk' ∧
    (∀ d ∈ outerWalk', Delta'.toCombMap.alpha d ∉ outerWalk') ∧
    dartWord Delta' (invDarts Delta' outerWalk') = dartWord Delta (invDarts Delta outerWalk) ∧
    (Delta'.relatorCells.filter fun C => C.face ∈ faces').length =
      (Delta.relatorCells.filter fun C => C.face ∈ faces).length ∧
    ∃ e : Fin Delta.rCellCount ≃ Fin Delta'.rCellCount, ∀ i,
      (cell Delta' (e i)).word = (cell Delta i).word ∧
        ((cell Delta' (e i)).face ∈ faces' ↔ (cell Delta i).face ∈ faces)

/-- **A bridge dart of a walk that turns to its successor lies on a face with at least two
darts.**  On a monogon `σ (α d) = d`, so the walk successor of `d` is `d`, and a walk without
repeated darts is then `[d]`, which does not hold `α d`. -/
theorem one_lt_faceBoundary_length_of_bridge {Delta : DiscDiagram.{u, w, v} W}
    {faces : Finset Delta.toCombMap.Face} {outerWalk : List Delta.toCombMap.Dart}
    (E : EnclosedFaceSetSucc Delta faces outerWalk) {d : Delta.toCombMap.Dart}
    (hd : d ∈ outerWalk) (had : Delta.toCombMap.alpha d ∈ outerWalk) :
    1 < (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts.length := by
  by_contra hle
  have hpos : 0 < (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts.length :=
    List.length_pos_iff.mpr (Delta.faceBoundary _).nonempty
  have hfix : Delta.toCombMap.facePerm d = d :=
    facePerm_eq_self_of_length_one _ (by omega) (((Delta.faceBoundary _).mem_iff d).mpr rfl)
  have hsig : Delta.toCombMap.sigma (Delta.toCombMap.alpha d) = d := by
    show (Delta.toCombMap.sigma * Delta.toCombMap.alpha) d = d
    exact hfix
  obtain ⟨i, hi, hid⟩ := List.getElem_of_mem hd
  have hkeep : walkKeep Delta.toCombMap outerWalk
      ((Delta.toCombMap.sigma ^ 1) (Delta.toCombMap.alpha outerWalk[i])) := by
    rw [pow_one, hid, hsig]
    exact Or.inl hd
  have hnext := E.turn_next i hi 1 Nat.one_pos hkeep (fun k hk hk1 => absurd hk1 (by omega))
  rw [pow_one, hid, hsig] at hnext
  have hnext' : outerWalk[i] = outerWalk[(i + 1) % outerWalk.length]'
      (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) := hid.trans hnext
  have hidx : i = (i + 1) % outerWalk.length := (E.nodup.getElem_inj_iff).mp hnext'
  have hlen1 : outerWalk.length = 1 := by
    rcases Nat.lt_or_ge (i + 1) outerWalk.length with h | h
    · rw [Nat.mod_eq_of_lt h] at hidx
      omega
    · have heq : i + 1 = outerWalk.length := by omega
      rw [heq, Nat.mod_self] at hidx
      omega
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen1
  have hd' : d = a := by
    rw [ha, List.mem_singleton] at hd
    exact hd
  have had' : Delta.toCombMap.alpha d = a := by
    rw [ha, List.mem_singleton] at had
    exact had
  exact Delta.toCombMap.alpha_fixedPointFree d (had'.trans hd'.symm)

open scoped Classical in
/-- **The induction on the number of bridge darts**, with no enclosed face required: the one-edge
tree walk `[e, ē]` encloses no face and still has a bridge. -/
theorem doublingOutputSucc (n : ℕ) :
    ∀ (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face)
      (outerWalk : List Delta.toCombMap.Dart), bridgeCount outerWalk = n →
      EnclosedFaceSetSucc Delta faces outerWalk → DoublingOutput Delta faces outerWalk := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Delta faces outerWalk hn E
  by_cases hfree : ∀ d ∈ outerWalk, Delta.toCombMap.alpha d ∉ outerWalk
  · exact ⟨Delta, faces, outerWalk, ⟨OEquivalentDiscDiagram.refl Delta⟩, E, hfree, rfl, rfl,
      Equiv.refl _, fun _ => ⟨rfl, Iff.rfl⟩⟩
  obtain ⟨d, hd, had⟩ : ∃ d ∈ outerWalk, Delta.toCombMap.alpha d ∈ outerWalk := by
    by_contra h
    exact hfree fun d hd had => h ⟨d, hd, had⟩
  obtain ⟨e, he, hae, hlen⟩ : ∃ e ∈ outerWalk, Delta.toCombMap.alpha e ∈ outerWalk ∧
      1 < (Delta.faceBoundary (Delta.toCombMap.faceOf e)).darts.length :=
    ⟨d, hd, had, one_lt_faceBoundary_length_of_bridge E hd had⟩
  by_cases hout : Delta.toCombMap.faceOf e = Delta.outerFace
  · -- the exterior branch
    have hmem : e ∈ (Delta.faceBoundary Delta.outerFace).darts :=
      ((Delta.faceBoundary _).mem_iff e).mpr hout
    obtain ⟨j, hj⟩ := exists_index_eq_dart Delta Delta.outerFace hmem
    have hlen' : 1 < (Delta.faceBoundary Delta.outerFace).darts.length := by
      rw [← hout]
      exact hlen
    rw [← hj] at he hae
    have E' := enclosedFaceSetSucc_spurDiagram Delta j hlen' E he hae
    have hlt := lt_of_lt_of_eq (bridgeCount_image_lt Delta Delta.outerFace j hlen' he hae) hn
    obtain ⟨Delta'', faces'', outerWalk'', ⟨equiv''⟩, E'', hfree'', hword'', hcount'', e'', he''⟩ :=
      ih _ hlt (OuterSpurThickening.diagram Delta j hlen') _ _ rfl E'
    obtain ⟨e₁, he₁⟩ := cellCorrespondence_map (Delta := Delta)
      (Delta' := OuterSpurThickening.diagram Delta j hlen')
      (faces := faces) (faces' := newFaces Delta Delta.outerFace j hlen' faces)
      (OuterSpurThickening.spurCell Delta j hlen') rfl (fun _ => rfl)
      (fun C => faceImage_mem_newFaces_iff Delta Delta.outerFace j hlen' faces C.face)
    refine ⟨Delta'', faces'', outerWalk'',
      ⟨(OuterSpurThickening.oEquivalent Delta j hlen').trans equiv''⟩, E'', hfree'', ?_, ?_,
      e₁.trans e'', fun i => ⟨(he'' (e₁ i)).1.trans (he₁ i).1, (he'' (e₁ i)).2.trans (he₁ i).2⟩⟩
    · rw [hword'']
      exact dartWord_invDarts_spurDiagram Delta j hlen' outerWalk
    · rw [hcount'']
      exact length_filter_spurDiagram Delta j hlen' faces
  · -- an inner face
    have hmem : e ∈ (Delta.faceBoundary (Delta.toCombMap.faceOf e)).darts :=
      ((Delta.faceBoundary _).mem_iff e).mpr rfl
    obtain ⟨j, hj⟩ := exists_index_eq_dart Delta (Delta.toCombMap.faceOf e) hmem
    rw [← hj] at he hae
    have E' := enclosedFaceSetSucc_diagram Delta (Delta.toCombMap.faceOf e) j hlen hout E he hae
    have hlt := lt_of_lt_of_eq
      (bridgeCount_image_lt Delta (Delta.toCombMap.faceOf e) j hlen he hae) hn
    obtain ⟨Delta'', faces'', outerWalk'', ⟨equiv''⟩, E'', hfree'', hword'', hcount'', e'', he''⟩ :=
      ih _ hlt (FaceEdgeDoubling.diagram Delta (Delta.toCombMap.faceOf e) j hlen hout) _ _ rfl E'
    obtain ⟨e₁, he₁⟩ := cellCorrespondence_map (Delta := Delta)
      (Delta' := FaceEdgeDoubling.diagram Delta (Delta.toCombMap.faceOf e) j hlen hout)
      (faces := faces) (faces' := newFaces Delta (Delta.toCombMap.faceOf e) j hlen faces)
      (FaceEdgeDoubling.cell Delta (Delta.toCombMap.faceOf e) j hlen hout) rfl (fun _ => rfl)
      (fun C => faceImage_mem_newFaces_iff Delta (Delta.toCombMap.faceOf e) j hlen faces C.face)
    refine ⟨Delta'', faces'', outerWalk'',
      ⟨(FaceEdgeDoubling.oEquivalent Delta (Delta.toCombMap.faceOf e) j hlen hout).trans equiv''⟩,
      E'', hfree'', ?_, ?_,
      e₁.trans e'', fun i => ⟨(he'' (e₁ i)).1.trans (he₁ i).1, (he'' (e₁ i)).2.trans (he₁ i).2⟩⟩
    · rw [hword'']
      exact dartWord_invDarts_diagram Delta (Delta.toCombMap.faceOf e) j hlen hout outerWalk
    · rw [hcount'']
      exact length_filter_diagram Delta (Delta.toCombMap.faceOf e) j hlen hout faces

open scoped Classical in
/-- **The induction, in its first form with an enclosed face.** -/
theorem doublingOutput (n : ℕ) :
    ∀ (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face)
      (outerWalk : List Delta.toCombMap.Dart), bridgeCount outerWalk = n →
      EnclosedFaceSetSucc Delta faces outerWalk → faces.Nonempty →
        DoublingOutput Delta faces outerWalk :=
  fun Delta faces outerWalk hn E _ => doublingOutputSucc n Delta faces outerWalk hn E

/-- **`EnclosedBridgeDoublingSuccStatement` holds.** -/
theorem enclosedBridgeDoublingSucc : EnclosedBridgeDoublingSuccStatement.{u, w, v} := by
  intro G _ Lambda W Delta faces outerWalk E _hne
  obtain ⟨Delta', faces', outerWalk', hequiv, E', hfree, hword, hcount, -⟩ :=
    doublingOutputSucc _ Delta faces outerWalk rfl E
  exact ⟨Delta', faces', outerWalk', hequiv, E', hfree, hword, hcount⟩

/-- **The successor-form singular least-area filter.** -/
theorem enclosedLeastAreaFilterSucc : EnclosedLeastAreaFilterSuccStatement.{u, w, v} :=
  EnclosedPocketRegion.enclosedLeastAreaFilterSucc_of_doubling enclosedBridgeDoublingSucc

end EnclosedBridgeDoubling

end GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen.EnclosedBridgeDoubling

#audit_axioms mem_pair_of_monogons
#audit_axioms exists_bridge_side
#audit_axioms cellCorrespondence_map
#audit_axioms one_lt_faceBoundary_length_of_bridge
#audit_axioms doublingOutputSucc
#audit_axioms doublingOutput
#audit_axioms enclosedBridgeDoublingSucc
#audit_axioms enclosedLeastAreaFilterSucc
