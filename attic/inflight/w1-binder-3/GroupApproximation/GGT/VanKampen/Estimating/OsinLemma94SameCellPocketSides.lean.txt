import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSidesDisjoint
import GroupApproximation.GGT.VanKampen.FaceSetWordHomotopyCore
import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.Meta.AxiomGuard

/-!
# The sides of the pocket walks of the one-cell pairs of Lemma 9.4, Case 1

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, for a backwards connector pair whose source and
target sides lie across one relator cell `Π`.  Some rotation of the face walk of the polygon face
`f` reads `X q⁻¹ Y p⁻¹`, with `p` and `q` nonempty arcs of `Π`, and some rotation of `∂Π` reads
`q B p A`.  The pocket walks are `invDarts X ++ invDarts B` and `invDarts Y ++ invDarts A`.  Any of
`X`, `Y`, `A`, `B` may be empty.

Every dart of either walk has `f` or `Π` across it.  The first dart of `p` gives an edge from `Π`
to `f` that lies off both walks, so `f` and `Π` lie in one face class of each walk.  A noncrossing
walk keeps the face across each of its darts off its side, so both `f` and `Π` are off the side of
each noncrossing pocket walk, in every window case.

* `SimpleClosedWalkSides.not_mem_sideFaces_of_two_faces`: the generic step, for a noncrossing
  closed walk with two faces across it and an edge between them off the walk.
* `SimpleClosedWalkSides.not_walkKeep_of_alpha_mem`: an edge off a walk made of darts reversed
  from two windows on two faces.
* `SimpleClosedWalkSides.disjoint_sideFaces_of_two_faces` and `not_mem_sideFaces_or_of_two_faces`:
  two such walks with no common dart have disjoint sides, and any face is off one of them.
* `SameCellPocketSides.exists_edge`: the first dart of `p`, off `B`, `A`, and reversed off `X`,
  `Y`.
* `SameCellPocketSides.face_not_mem_sideFaces_X` and `_Y`: `f` and `Π` are off the side of each
  noncrossing pocket walk; `Π` off the side is the input `hi` of the loop cut.
* `SameCellPocketSides.disjoint_sideFaces` and `not_mem_sideFaces_or`: the two pocket walks have
  disjoint sides, so the exterior face is off one of them.

No barrier nonemptiness is needed, so the cases with an empty window are covered as they are.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

namespace SimpleClosedWalkSides

variable {M : CombMap.{v}}

/-- **Two faces across an edge off the walk lie on the same side.** -/
theorem mem_sideFaces_iff_of_not_walkKeep (w : List M.Dart) {e : M.Dart}
    (hk : ¬ walkKeep M w e) :
    M.faceOf e ∈ sideFaces M w ↔ M.faceOf (M.alpha e) ∈ sideFaces M w :=
  mem_sideFaces_iff_of_eqvGen w (x := e) (z := M.alpha e) (.rel _ _ (Or.inr ⟨hk, rfl⟩))

/-- **Both faces off the side.**  Every dart of a noncrossing closed walk has `F₁` or `F₂` across
it, and an edge off the walk joins `F₂` to `F₁`.  The face across a walk dart is off the side, and
the edge puts `F₁` and `F₂` in one face class, so both are off the side. -/
theorem not_mem_sideFaces_of_two_faces (hM : M.IsPlanar) {w : List M.Dart}
    (hw : IsNoncrossingClosedWalk M w) {F₁ F₂ : M.Face}
    (hacross : ∀ d ∈ w, M.faceOf (M.alpha d) = F₁ ∨ M.faceOf (M.alpha d) = F₂)
    {e : M.Dart} (he₁ : M.faceOf e = F₂) (he₂ : M.faceOf (M.alpha e) = F₁)
    (hk : ¬ walkKeep M w e) :
    F₁ ∉ sideFaces M w ∧ F₂ ∉ sideFaces M w := by
  have htransfer := mem_sideFaces_iff_of_not_walkKeep w hk
  rw [he₁, he₂] at htransfer
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil w hw.ne_nil
  have hoff : M.faceOf (M.alpha d) ∉ sideFaces M w :=
    (show M.faceOf d ∈ sideFaces M w ∧ M.faceOf (M.alpha d) ∉ sideFaces M w from
      (hw.isBoundaryDart_sideFaces_iff hM d).mpr hd).2
  rcases hacross d hd with h | h
  · rw [h] at hoff
    exact ⟨hoff, fun h₂ => hoff (htransfer.mp h₂)⟩
  · rw [h] at hoff
    exact ⟨fun h₁ => hoff (htransfer.mpr h₁), hoff⟩

/-- **The faces across a walk made of reversed window darts.** -/
theorem faceOf_alpha_eq_or_of_alpha_mem {w Z₁ Z₂ : List M.Dart} {F₁ F₂ : M.Face}
    (hZ₁ : ∀ z ∈ Z₁, M.faceOf z = F₁) (hZ₂ : ∀ z ∈ Z₂, M.faceOf z = F₂)
    (hw : ∀ d ∈ w, M.alpha d ∈ Z₁ ∨ M.alpha d ∈ Z₂) :
    ∀ d ∈ w, M.faceOf (M.alpha d) = F₁ ∨ M.faceOf (M.alpha d) = F₂ := by
  intro d hd
  rcases hw d hd with h | h
  · exact Or.inl (hZ₁ _ h)
  · exact Or.inr (hZ₂ _ h)

/-- **An edge off a walk made of reversed window darts.**  The walk reverses darts of `Z₁`, on the
face `F₁`, and of `Z₂`, on the face `F₂ ≠ F₁`.  An edge from `F₂` to `F₁` whose dart on `F₂` is off
`Z₂` and whose dart on `F₁` is off `Z₁` is not an edge of the walk. -/
theorem not_walkKeep_of_alpha_mem {w Z₁ Z₂ : List M.Dart} {F₁ F₂ : M.Face} (hF : F₁ ≠ F₂)
    (hZ₁ : ∀ z ∈ Z₁, M.faceOf z = F₁) (hZ₂ : ∀ z ∈ Z₂, M.faceOf z = F₂)
    (hw : ∀ d ∈ w, M.alpha d ∈ Z₁ ∨ M.alpha d ∈ Z₂)
    {e : M.Dart} (he₁ : M.faceOf e = F₂) (he₂ : M.faceOf (M.alpha e) = F₁)
    (heZ₂ : e ∉ Z₂) (heZ₁ : M.alpha e ∉ Z₁) : ¬ walkKeep M w e := by
  rintro (hmem | hmem)
  · rcases hw e hmem with h | h
    · exact heZ₁ h
    · exact hF (he₂.symm.trans (hZ₂ _ h))
  · rcases hw (M.alpha e) hmem with h | h
    · rw [M.alpha_involutive e] at h
      exact hF ((hZ₁ _ h).symm.trans he₁)
    · rw [M.alpha_involutive e] at h
      exact heZ₂ h

/-- **Two walks across the same two faces have disjoint sides**, when they are noncrossing, share
no dart, and an edge between the two faces lies off both. -/
theorem disjoint_sideFaces_of_two_faces (hM : M.IsPlanar) {w₁ w₂ : List M.Dart}
    (hw₁ : IsNoncrossingClosedWalk M w₁) (hw₂ : IsNoncrossingClosedWalk M w₂) {F₁ F₂ : M.Face}
    (hacross₁ : ∀ d ∈ w₁, M.faceOf (M.alpha d) = F₁ ∨ M.faceOf (M.alpha d) = F₂)
    (hacross₂ : ∀ d ∈ w₂, M.faceOf (M.alpha d) = F₁ ∨ M.faceOf (M.alpha d) = F₂)
    {e : M.Dart} (he₁ : M.faceOf e = F₂) (he₂ : M.faceOf (M.alpha e) = F₁)
    (hk₁ : ¬ walkKeep M w₁ e) (hk₂ : ¬ walkKeep M w₂ e) (hcommon : ∀ d ∈ w₂, d ∉ w₁) :
    Disjoint (sideFaces M w₁) (sideFaces M w₂) := by
  have h₁ := not_mem_sideFaces_of_two_faces hM hw₁ hacross₁ he₁ he₂ hk₁
  have h₂ := not_mem_sideFaces_of_two_faces hM hw₂ hacross₂ he₁ he₂ hk₂
  refine disjoint_sideFaces_of_across_of_not_mem (fun d hd => ?_) (fun d hd => ?_) hcommon
  · rcases hacross₁ d hd with h | h
    · rw [h]
      exact h₂.1
    · rw [h]
      exact h₂.2
  · rcases hacross₂ d hd with h | h
    · rw [h]
      exact h₁.1
    · rw [h]
      exact h₁.2

/-- **Any face is off one of the two sides**, in the setting of
`disjoint_sideFaces_of_two_faces`. -/
theorem not_mem_sideFaces_or_of_two_faces (hM : M.IsPlanar) {w₁ w₂ : List M.Dart}
    (hw₁ : IsNoncrossingClosedWalk M w₁) (hw₂ : IsNoncrossingClosedWalk M w₂) {F₁ F₂ : M.Face}
    (hacross₁ : ∀ d ∈ w₁, M.faceOf (M.alpha d) = F₁ ∨ M.faceOf (M.alpha d) = F₂)
    (hacross₂ : ∀ d ∈ w₂, M.faceOf (M.alpha d) = F₁ ∨ M.faceOf (M.alpha d) = F₂)
    {e : M.Dart} (he₁ : M.faceOf e = F₂) (he₂ : M.faceOf (M.alpha e) = F₁)
    (hk₁ : ¬ walkKeep M w₁ e) (hk₂ : ¬ walkKeep M w₂ e) (hcommon : ∀ d ∈ w₂, d ∉ w₁)
    (F : M.Face) : F ∉ sideFaces M w₁ ∨ F ∉ sideFaces M w₂ := by
  by_cases h : F ∈ sideFaces M w₁
  · exact Or.inr (Finset.disjoint_left.mp
      (disjoint_sideFaces_of_two_faces hM hw₁ hw₂ hacross₁ hacross₂ he₁ he₂ hk₁ hk₂ hcommon) h)
  · exact Or.inl h

end SimpleClosedWalkSides

open Embedded SimpleClosedWalkSides

namespace SameCellPocketSides

/-- **Parts of a four-part list with no repeated element.** -/
theorem nodup_append_four {α : Type*} {L₁ L₂ L₃ L₄ : List α} (h : (L₁ ++ L₂ ++ L₃ ++ L₄).Nodup) :
    (∀ x ∈ L₁ ++ L₂, ∀ y ∈ L₃, x ≠ y) ∧ (∀ x ∈ L₁ ++ L₂ ++ L₃, ∀ y ∈ L₄, x ≠ y) := by
  have h' := List.nodup_append.mp h
  exact ⟨(List.nodup_append.mp h'.1).2.2, h'.2.2⟩

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- A dart of `invDarts l` reverses a dart of `l`. -/
theorem alpha_mem_of_mem_invDarts {l : List Delta.toCombMap.Dart} {d : Delta.toCombMap.Dart}
    (hd : d ∈ invDarts Delta l) : Delta.toCombMap.alpha d ∈ l := by
  change d ∈ l.reverse.map Delta.toCombMap.alpha at hd
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
  rw [Delta.toCombMap.alpha_involutive x]
  exact List.mem_reverse.mp hx

/-- A dart of `invDarts l ++ invDarts l'` reverses a dart of `l` or of `l'`. -/
theorem alpha_mem_of_mem_invDarts_append {l l' : List Delta.toCombMap.Dart}
    {d : Delta.toCombMap.Dart} (hd : d ∈ invDarts Delta l ++ invDarts Delta l') :
    Delta.toCombMap.alpha d ∈ l ∨ Delta.toCombMap.alpha d ∈ l' := by
  rcases List.mem_append.mp hd with h | h
  · exact Or.inl (alpha_mem_of_mem_invDarts h)
  · exact Or.inr (alpha_mem_of_mem_invDarts h)

/-- Darts of a rotation of the face walk of `f` lie on `f`. -/
theorem faceOf_of_mem_rotate {f : Delta.toCombMap.Face} {r : ℕ} {L : List Delta.toCombMap.Dart}
    (htrav : (Delta.faceBoundary f).darts.rotate r = L) {d : Delta.toCombMap.Dart} (hd : d ∈ L) :
    Delta.toCombMap.faceOf d = f := by
  have hrot : d ∈ (Delta.faceBoundary f).darts.rotate r := by
    rw [htrav]
    exact hd
  exact ((Delta.faceBoundary f).mem_iff d).mp (List.mem_rotate.mp hrot)

/-- Darts of a rotation of the carrier of the cell `j` lie on its face. -/
theorem faceOf_of_mem_cellDarts_rotate {j : Fin Delta.rCellCount} {n : ℕ}
    {L : List Delta.toCombMap.Dart} (hPi : (cellDarts Delta j).rotate n = L)
    {d : Delta.toCombMap.Dart} (hd : d ∈ L) :
    Delta.toCombMap.faceOf d = (cell Delta j).face := by
  have hrot : d ∈ (cellDarts Delta j).rotate n := by
    rw [hPi]
    exact hd
  exact ((Delta.faceBoundary (cell Delta j).face).mem_iff d).mp (List.mem_rotate.mp hrot)

/-- **The first dart of `p`.**  It lies on `Π`, its reversal lies on `f`, it is off `B` and `A`,
and its reversal is off `X` and `Y`. -/
theorem exists_edge {f : Delta.toCombMap.Face} {j : Fin Delta.rCellCount}
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {X Y : List Delta.toCombMap.Dart}
    {r : ℕ} (htrav : (Delta.faceBoundary f).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    {B A : List Delta.toCombMap.Dart} {n : ℕ}
    (hPi : (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    (hs : 0 < sourceArc.length) :
    ∃ e : Delta.toCombMap.Dart, Delta.toCombMap.faceOf e = (cell Delta j).face ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha e) = f ∧ e ∉ B ∧ e ∉ A ∧
        Delta.toCombMap.alpha e ∉ X ∧ Delta.toCombMap.alpha e ∉ Y := by
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil sourceArc.darts (by
    intro hnil
    have h := sourceArc.darts_length
    rw [hnil, List.length_nil] at h
    omega)
  have heα : Delta.toCombMap.alpha e ∈ sourceArc.reverseDarts := by
    show Delta.toCombMap.alpha e ∈ sourceArc.darts.reverse.map Delta.toCombMap.alpha
    exact List.mem_map.mpr ⟨e, List.mem_reverse.mpr he, rfl⟩
  have hwalk : (X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts).Nodup := by
    rw [← htrav]
    exact List.nodup_rotate.mpr (Delta.faceBoundary f).nodup
  have hcarrier : (targetArc.darts ++ B ++ sourceArc.darts ++ A).Nodup := by
    rw [← hPi]
    exact List.nodup_rotate.mpr (Delta.faceBoundary (cell Delta j).face).nodup
  refine ⟨e, faceOf_of_mem_cellDarts_rotate hPi
      (List.mem_append_left A (List.mem_append_right _ he)),
    faceOf_of_mem_rotate htrav (List.mem_append_right _ heα), fun hB => ?_, fun hA => ?_,
    fun hX => ?_, fun hY => ?_⟩
  · exact (nodup_append_four hcarrier).1 _ (List.mem_append_right _ hB) _ he rfl
  · exact (nodup_append_four hcarrier).2 _ (List.mem_append_right _ he) _ hA rfl
  · exact (nodup_append_four hwalk).2 _
      (List.mem_append_left _ (List.mem_append_left _ hX)) _ heα rfl
  · exact (nodup_append_four hwalk).2 _ (List.mem_append_right _ hY) _ heα rfl

/-- **The two pocket walks share no dart.**  The face walk and the carrier have no repeated dart,
and `f` is not the face of `Π`. -/
theorem not_mem_walk_of_mem_walk {f : Delta.toCombMap.Face} {j : Fin Delta.rCellCount}
    (hf : (cell Delta j).face ≠ f)
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {X Y : List Delta.toCombMap.Dart}
    {r : ℕ} (htrav : (Delta.faceBoundary f).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    {B A : List Delta.toCombMap.Dart} {n : ℕ}
    (hPi : (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A) :
    ∀ d ∈ invDarts Delta Y ++ invDarts Delta A, d ∉ invDarts Delta X ++ invDarts Delta B := by
  intro d hd₂ hd₁
  have hwalk : (X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts).Nodup := by
    rw [← htrav]
    exact List.nodup_rotate.mpr (Delta.faceBoundary f).nodup
  have hcarrier : (targetArc.darts ++ B ++ sourceArc.darts ++ A).Nodup := by
    rw [← hPi]
    exact List.nodup_rotate.mpr (Delta.faceBoundary (cell Delta j).face).nodup
  rcases alpha_mem_of_mem_invDarts_append hd₂ with hY | hA <;>
    rcases alpha_mem_of_mem_invDarts_append hd₁ with hX | hB
  · exact (nodup_append_four hwalk).1 _ (List.mem_append_left _ hX) _ hY rfl
  · exact hf ((faceOf_of_mem_cellDarts_rotate hPi
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hB)))).symm.trans
      (faceOf_of_mem_rotate htrav (List.mem_append_left _ (List.mem_append_right _ hY))))
  · exact hf ((faceOf_of_mem_cellDarts_rotate hPi (List.mem_append_right _ hA)).symm.trans
      (faceOf_of_mem_rotate htrav
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hX)))))
  · exact (nodup_append_four hcarrier).2 _
      (List.mem_append_left _ (List.mem_append_right _ hB)) _ hA rfl

/-- **`f` and `Π` off the pocket across `X`.**  For the noncrossing pocket walk
`invDarts X ++ invDarts B`, whether or not `X` or `B` is empty. -/
theorem face_not_mem_sideFaces_X {f : Delta.toCombMap.Face} {j : Fin Delta.rCellCount}
    (hf : (cell Delta j).face ≠ f)
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {X Y : List Delta.toCombMap.Dart}
    {r : ℕ} (htrav : (Delta.faceBoundary f).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    {B A : List Delta.toCombMap.Dart} {n : ℕ}
    (hPi : (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    (hs : 0 < sourceArc.length)
    (hw : IsNoncrossingClosedWalk Delta.toCombMap (invDarts Delta X ++ invDarts Delta B)) :
    f ∉ sideFaces Delta.toCombMap (invDarts Delta X ++ invDarts Delta B) ∧
      (cell Delta j).face ∉ sideFaces Delta.toCombMap (invDarts Delta X ++ invDarts Delta B) := by
  obtain ⟨e, he₁, he₂, heB, -, heX, -⟩ := exists_edge sourceArc targetArc htrav hPi hs
  have hX : ∀ z ∈ X, Delta.toCombMap.faceOf z = f := fun z hz => faceOf_of_mem_rotate htrav
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hz)))
  have hB : ∀ z ∈ B, Delta.toCombMap.faceOf z = (cell Delta j).face := fun z hz =>
    faceOf_of_mem_cellDarts_rotate hPi
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hz)))
  have hmem : ∀ d ∈ invDarts Delta X ++ invDarts Delta B,
      Delta.toCombMap.alpha d ∈ X ∨ Delta.toCombMap.alpha d ∈ B :=
    fun _ hd => alpha_mem_of_mem_invDarts_append hd
  exact not_mem_sideFaces_of_two_faces Delta.planar hw (faceOf_alpha_eq_or_of_alpha_mem hX hB hmem)
    he₁ he₂ (not_walkKeep_of_alpha_mem (Ne.symm hf) hX hB hmem he₁ he₂ heB heX)

/-- **`f` and `Π` off the pocket across `Y`.**  For the noncrossing pocket walk
`invDarts Y ++ invDarts A`, whether or not `Y` or `A` is empty. -/
theorem face_not_mem_sideFaces_Y {f : Delta.toCombMap.Face} {j : Fin Delta.rCellCount}
    (hf : (cell Delta j).face ≠ f)
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {X Y : List Delta.toCombMap.Dart}
    {r : ℕ} (htrav : (Delta.faceBoundary f).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    {B A : List Delta.toCombMap.Dart} {n : ℕ}
    (hPi : (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    (hs : 0 < sourceArc.length)
    (hw : IsNoncrossingClosedWalk Delta.toCombMap (invDarts Delta Y ++ invDarts Delta A)) :
    f ∉ sideFaces Delta.toCombMap (invDarts Delta Y ++ invDarts Delta A) ∧
      (cell Delta j).face ∉ sideFaces Delta.toCombMap (invDarts Delta Y ++ invDarts Delta A) := by
  obtain ⟨e, he₁, he₂, -, heA, -, heY⟩ := exists_edge sourceArc targetArc htrav hPi hs
  have hY : ∀ z ∈ Y, Delta.toCombMap.faceOf z = f := fun z hz => faceOf_of_mem_rotate htrav
    (List.mem_append_left _ (List.mem_append_right _ hz))
  have hA : ∀ z ∈ A, Delta.toCombMap.faceOf z = (cell Delta j).face := fun z hz =>
    faceOf_of_mem_cellDarts_rotate hPi (List.mem_append_right _ hz)
  have hmem : ∀ d ∈ invDarts Delta Y ++ invDarts Delta A,
      Delta.toCombMap.alpha d ∈ Y ∨ Delta.toCombMap.alpha d ∈ A :=
    fun _ hd => alpha_mem_of_mem_invDarts_append hd
  exact not_mem_sideFaces_of_two_faces Delta.planar hw (faceOf_alpha_eq_or_of_alpha_mem hY hA hmem)
    he₁ he₂ (not_walkKeep_of_alpha_mem (Ne.symm hf) hY hA hmem he₁ he₂ heA heY)

/-- **The two pocket walks have disjoint sides**, when both are noncrossing, in every window
case. -/
theorem disjoint_sideFaces {f : Delta.toCombMap.Face} {j : Fin Delta.rCellCount}
    (hf : (cell Delta j).face ≠ f)
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {X Y : List Delta.toCombMap.Dart}
    {r : ℕ} (htrav : (Delta.faceBoundary f).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    {B A : List Delta.toCombMap.Dart} {n : ℕ}
    (hPi : (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    (hs : 0 < sourceArc.length)
    (hw₁ : IsNoncrossingClosedWalk Delta.toCombMap (invDarts Delta X ++ invDarts Delta B))
    (hw₂ : IsNoncrossingClosedWalk Delta.toCombMap (invDarts Delta Y ++ invDarts Delta A)) :
    Disjoint (sideFaces Delta.toCombMap (invDarts Delta X ++ invDarts Delta B))
      (sideFaces Delta.toCombMap (invDarts Delta Y ++ invDarts Delta A)) := by
  have h₁ := face_not_mem_sideFaces_X hf sourceArc targetArc htrav hPi hs hw₁
  have h₂ := face_not_mem_sideFaces_Y hf sourceArc targetArc htrav hPi hs hw₂
  have hcommon := not_mem_walk_of_mem_walk hf sourceArc targetArc htrav hPi
  have hX : ∀ z ∈ X, Delta.toCombMap.faceOf z = f := fun z hz => faceOf_of_mem_rotate htrav
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hz)))
  have hB : ∀ z ∈ B, Delta.toCombMap.faceOf z = (cell Delta j).face := fun z hz =>
    faceOf_of_mem_cellDarts_rotate hPi
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hz)))
  have hY : ∀ z ∈ Y, Delta.toCombMap.faceOf z = f := fun z hz => faceOf_of_mem_rotate htrav
    (List.mem_append_left _ (List.mem_append_right _ hz))
  have hA : ∀ z ∈ A, Delta.toCombMap.faceOf z = (cell Delta j).face := fun z hz =>
    faceOf_of_mem_cellDarts_rotate hPi (List.mem_append_right _ hz)
  have hacross₁ := faceOf_alpha_eq_or_of_alpha_mem hX hB
    (fun _ hd => alpha_mem_of_mem_invDarts_append hd)
  have hacross₂ := faceOf_alpha_eq_or_of_alpha_mem hY hA
    (fun _ hd => alpha_mem_of_mem_invDarts_append hd)
  refine disjoint_sideFaces_of_across_of_not_mem (fun d hd => ?_) (fun d hd => ?_) hcommon
  · rcases hacross₁ d hd with h | h
    · rw [h]
      exact h₂.1
    · rw [h]
      exact h₂.2
  · rcases hacross₂ d hd with h | h
    · rw [h]
      exact h₁.1
    · rw [h]
      exact h₁.2

/-- **The exterior face is off one of the two pocket sides**, and so is any other face.  This is
the input `hout` of `PocketRegion.ofNoncrossingClosedWalk` for one of the two pocket walks. -/
theorem not_mem_sideFaces_or {f : Delta.toCombMap.Face} {j : Fin Delta.rCellCount}
    (hf : (cell Delta j).face ≠ f)
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {X Y : List Delta.toCombMap.Dart}
    {r : ℕ} (htrav : (Delta.faceBoundary f).darts.rotate r =
      X ++ targetArc.reverseDarts ++ Y ++ sourceArc.reverseDarts)
    {B A : List Delta.toCombMap.Dart} {n : ℕ}
    (hPi : (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    (hs : 0 < sourceArc.length)
    (hw₁ : IsNoncrossingClosedWalk Delta.toCombMap (invDarts Delta X ++ invDarts Delta B))
    (hw₂ : IsNoncrossingClosedWalk Delta.toCombMap (invDarts Delta Y ++ invDarts Delta A))
    (F : Delta.toCombMap.Face) :
    F ∉ sideFaces Delta.toCombMap (invDarts Delta X ++ invDarts Delta B) ∨
      F ∉ sideFaces Delta.toCombMap (invDarts Delta Y ++ invDarts Delta A) := by
  by_cases h : F ∈ sideFaces Delta.toCombMap (invDarts Delta X ++ invDarts Delta B)
  · exact Or.inr (Finset.disjoint_left.mp
      (disjoint_sideFaces hf sourceArc targetArc htrav hPi hs hw₁ hw₂) h)
  · exact Or.inl h

end SameCellPocketSides

end GroupApproximation.GGT.VanKampen

#audit_axioms
  GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides.mem_sideFaces_iff_of_not_walkKeep
#audit_axioms
  GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides.not_mem_sideFaces_of_two_faces
#audit_axioms
  GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides.faceOf_alpha_eq_or_of_alpha_mem
#audit_axioms GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides.not_walkKeep_of_alpha_mem
#audit_axioms
  GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides.disjoint_sideFaces_of_two_faces
#audit_axioms
  GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides.not_mem_sideFaces_or_of_two_faces
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketSides.nodup_append_four
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketSides.alpha_mem_of_mem_invDarts
#audit_axioms
  GroupApproximation.GGT.VanKampen.SameCellPocketSides.alpha_mem_of_mem_invDarts_append
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketSides.faceOf_of_mem_rotate
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketSides.faceOf_of_mem_cellDarts_rotate
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketSides.exists_edge
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketSides.not_mem_walk_of_mem_walk
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketSides.face_not_mem_sideFaces_X
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketSides.face_not_mem_sideFaces_Y
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketSides.disjoint_sideFaces
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellPocketSides.not_mem_sideFaces_or
