import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPinchCornerDigon
import GroupApproximation.Meta.AxiomGuard

/-!
# Good corners for the split of an outer pinch

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  A vertex split (`PinchSplit.Input`) needs the corners of its darts on
distinct faces that are neither the exterior nor relator faces, and the section pinch step needs them
off the face set.  Such a corner face is good (`OuterPinchCornerGood.GoodFace`).  A digon made by a
corner fix is good (`Estimating/OsinPocketOuterPinchCornerDigon.lean`).  An inner monogon is good over
relator words longer than one letter.  Goodness survives a later doubling or thickening on the image
face, and a corner off the doubled dart keeps its face image.

* `OuterPinchCornerGood.GoodFace`, `inputOfGood`, `inputOfGood_avoids`: a split from good corners.
* `OuterPinchCornerGood.not_cell_of_length_le_one`, `eq_of_faceOf_eq_of_length_le_one`: monogons.
* `OuterPinchCornerGood.exists_dart_eq_of_face`: the index of a dart in the traversal of a face.
* `OuterPinchCornerGood.next_ne_self`, `chordData_init`, `ChordData.withY`, `ChordData.x_ne_d₀`: the
  turn data.
* `PocketFaceSet.sameCycle_of_chordData`, `mem_ne_next_of_chordData`: in walk order.
* `PocketFaceSet.goodFace_faceImage_faceEdgeDoubling`, `goodFace_faceImage_outerSpurThickening`,
  `faceOf_alpha_embed_of_ne_faceEdgeDoubling`, `faceOf_alpha_embed_of_ne_outerSpurThickening`: across a
  later fix.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides
open scoped Classical

namespace OuterPinchCornerGood

open OuterPinchIsolated OuterPinchTransport

section Faces

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A good corner face**: neither the exterior nor a relator face, and off the face set. -/
def GoodFace (X : DiscDiagram.{u, w, v} W) (s : Finset X.toCombMap.Face)
    (g : X.toCombMap.Face) : Prop :=
  g ≠ X.outerFace ∧ (∀ C ∈ X.relatorCells, C.face ≠ g) ∧ g ∉ s

/-- **A split from good corners on distinct faces.** -/
noncomputable def inputOfGood {X : DiscDiagram.{u, w, v} W} {s : Finset X.toCombMap.Face}
    {x y : X.toCombMap.Dart} (hsame : X.toCombMap.sigma.SameCycle x y)
    (hx : GoodFace X s (X.toCombMap.faceOf (X.toCombMap.alpha x)))
    (hy : GoodFace X s (X.toCombMap.faceOf (X.toCombMap.alpha y)))
    (hne : X.toCombMap.faceOf (X.toCombMap.alpha x) ≠ X.toCombMap.faceOf (X.toCombMap.alpha y)) :
    PinchSplit.Input X where
  x := x
  y := y
  same_vertex := hsame
  cycles := Classical.choice (PinchSplit.exists_cycles hne)
  left_ne_outer := hx.1
  right_ne_outer := hy.1
  left_not_cell := hx.2.1
  right_not_cell := hy.2.1

/-- The split from good corners avoids the face set. -/
theorem inputOfGood_avoids {X : DiscDiagram.{u, w, v} W} {s : Finset X.toCombMap.Face}
    {x y : X.toCombMap.Dart} (hsame : X.toCombMap.sigma.SameCycle x y)
    (hx : GoodFace X s (X.toCombMap.faceOf (X.toCombMap.alpha x)))
    (hy : GoodFace X s (X.toCombMap.faceOf (X.toCombMap.alpha y)))
    (hne : X.toCombMap.faceOf (X.toCombMap.alpha x) ≠ X.toCombMap.faceOf (X.toCombMap.alpha y)) :
    (inputOfGood hsame hx hy hne).Avoids s :=
  ⟨hx.2.2, hy.2.2⟩

/-- **A face with at most one dart is not a relator face**, over relator words longer than one
letter. -/
theorem not_cell_of_length_le_one (X : DiscDiagram.{u, w, v} W) (hW : ∀ word ∈ W, 1 < word.length)
    {g : X.toCombMap.Face} (hg : (X.faceBoundary g).darts.length ≤ 1) :
    ∀ C ∈ X.relatorCells, C.face ≠ g := by
  intro C hC hCg
  have h := CornerCount.one_lt_length_of_relatorCell X hW hC
  rw [hCg] at h
  omega

/-- **Two darts of a face with at most one dart are equal.** -/
theorem eq_of_faceOf_eq_of_length_le_one (X : DiscDiagram.{u, w, v} W) {x y : X.toCombMap.Dart}
    (hle : (X.faceBoundary (X.toCombMap.faceOf x)).darts.length ≤ 1)
    (h : X.toCombMap.faceOf y = X.toCombMap.faceOf x) : y = x :=
  PocketTouchCorner.eq_of_mem_of_length_le_one _ hle _
    (((X.faceBoundary (X.toCombMap.faceOf x)).mem_iff y).mpr h) _
    (((X.faceBoundary (X.toCombMap.faceOf x)).mem_iff x).mpr rfl)

/-- **The index of a dart in the traversal of a face.** -/
theorem exists_dart_eq_of_face (X : DiscDiagram.{u, w, v} W) {f : X.toCombMap.Face}
    {d : X.toCombMap.Dart} (hd : X.toCombMap.faceOf d = f) :
    ∃ j : Fin (X.faceBoundary f).darts.length, FaceEdgeDoubling.dart X f j = d := by
  obtain ⟨n, hn⟩ := List.mem_iff_get.mp (((X.faceBoundary f).mem_iff d).mpr hd)
  exact ⟨n, (FaceEdgeDoubling.dart_eq_get X f n).trans hn⟩

end Faces

section Turn

variable {α : Type*}

/-- **In a list with two distinct entries, no entry is its own successor.** -/
theorem next_ne_self {l : List α} (hnodup : l.Nodup) {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : l.next a ha ≠ a := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
  have hlen : 1 < l.length := by
    by_contra hle
    obtain rfl : i = k := by omega
    exact hab rfl
  rw [List.next_getElem l hnodup i hi]
  intro h
  rw [List.Nodup.getElem_inj_iff hnodup] at h
  by_cases hlt : i + 1 < l.length
  · rw [Nat.mod_eq_of_lt hlt] at h
    omega
  · have hn : i + 1 = l.length := by omega
    rw [hn, Nat.mod_self] at h
    omega

variable {M : CombMap.{u}}

/-- **The chord data at a turn**, with `x = e₀` and `y` the dart before `alpha d₀`. -/
theorem chordData_init {c : List M.Dart} {d₀ e₀ : M.Dart} (hd₀ : d₀ ∈ c)
    (hnext₀ : c.next d₀ hd₀ = e₀)
    (huncross : ∀ d (hd : d ∈ c), d ≠ d₀ → M.sigma.SameCycle (M.alpha d₀) (M.alpha d) →
      (RotationBetween M (M.alpha d₀) e₀ (M.alpha d) ↔
        RotationBetween M (M.alpha d₀) e₀ (c.next d hd)))
    (hnot : ¬ FirstTurn M (c.reverse.map M.alpha) (M.alpha e₀) (M.alpha d₀)) :
    ChordData M c d₀ e₀ e₀ (M.sigma⁻¹ (M.alpha d₀)) where
  mem := hd₀
  next_eq := hnext₀
  uncrossed := huncross
  not_firstTurn := hnot
  run_x := ⟨0, by rw [pow_zero, Equiv.Perm.one_apply], fun _ ht0 ht => absurd ht (by omega)⟩
  run_y := ⟨1, Nat.one_pos, by rw [pow_one, Equiv.Perm.apply_inv_self],
    fun _ ht0 ht1 => absurd ht1 (by omega)⟩

/-- **The chord data with `y` the dart before `alpha d₀`.** -/
theorem ChordData.withY {c : List M.Dart} {d₀ e₀ x y : M.Dart} (H : ChordData M c d₀ e₀ x y) :
    ChordData M c d₀ e₀ x (M.sigma⁻¹ (M.alpha d₀)) :=
  { H with
    run_y := ⟨1, Nat.one_pos, by rw [pow_one, Equiv.Perm.apply_inv_self],
      fun _ ht0 ht1 => absurd ht1 (by omega)⟩ }

/-- **The x-corner dart is not `d₀`**: it is `e₀`, or a dart off the edges of the list. -/
theorem ChordData.x_ne_d₀ {c : List M.Dart} {d₀ e₀ x y : M.Dart} (H : ChordData M c d₀ e₀ x y)
    (hde : d₀ ≠ e₀) : x ≠ d₀ := by
  intro hx
  obtain ⟨m, hm, hkeepm⟩ := H.run_x
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0, pow_zero, Equiv.Perm.one_apply, hx] at hm
    exact hde hm.symm
  · refine hkeepm m hpos le_rfl ?_
    rw [hm, hx]
    exact Or.inl H.mem

end Turn

end OuterPinchCornerGood

open OuterPinchIsolated OuterPinchCorners OuterPinchTransport OuterPinchCornerGood

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The split darts of chord data lie at one vertex**, in walk order. -/
theorem sameCycle_of_chordData (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    {d₀ e₀ x y : X.toCombMap.Dart} (H : ChordData X.toCombMap K.boundary.cycle d₀ e₀ x y) :
    X.toCombMap.sigma.SameCycle x y := by
  obtain ⟨m, hm, -⟩ := H.run_x
  obtain ⟨q, -, hq, -⟩ := H.run_y
  have hvert : X.toCombMap.vertexOf (X.toCombMap.alpha d₀) = X.toCombMap.vertexOf e₀ := by
    have h := rel_next_of_isChain K.boundary.cycle_nonempty K.boundary.cycle_nodup hK.1 hK.2 H.mem
    rwa [H.next_eq] at h
  exact ((sameCycle_of_pow_eq hm).symm.trans
    ((X.toCombMap.vertexOf_eq_iff _ _).mp hvert).symm).trans (sameCycle_of_pow_eq hq).symm

/-- **The turn of chord data is not a loop of the boundary cycle**, in walk order. -/
theorem mem_ne_next_of_chordData (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    {d₀ e₀ x y : X.toCombMap.Dart} (H : ChordData X.toCombMap K.boundary.cycle d₀ e₀ x y) :
    d₀ ≠ e₀ := by
  intro hde
  have hc : ∀ d ∈ K.boundary.cycle, X.toCombMap.alpha d ∉ K.boundary.cycle :=
    fun d hd => K.boundary_alpha_not_mem hd
  have he₀ : e₀ ∈ K.boundary.cycle := by
    rw [← H.next_eq]
    exact List.next_mem ..
  have hαe : X.toCombMap.alpha d₀ ≠ e₀ := fun h => hc d₀ H.mem (by rw [h]; exact he₀)
  have hvert : X.toCombMap.vertexOf (X.toCombMap.alpha d₀) = X.toCombMap.vertexOf e₀ := by
    have h := rel_next_of_isChain K.boundary.cycle_nonempty K.boundary.cycle_nodup hK.1 hK.2 H.mem
    rwa [H.next_eq] at h
  obtain ⟨k₀, -, hk₀, hk₀min⟩ :=
    exists_firstArrival ((X.toCombMap.vertexOf_eq_iff _ _).mp hvert) hαe
  obtain ⟨z₀, hz₀, -, hz₀e, -⟩ := exists_outside_of_not_firstTurn
    K.boundary.cycle_nonempty K.boundary.cycle_nodup hc hK.1 hK.2 H.mem H.next_eq H.uncrossed hk₀
    hk₀min H.not_firstTurn
  exact next_ne_self K.boundary.cycle_nodup H.mem hz₀ (fun h => hz₀e (h.symm.trans hde))
    (H.next_eq.trans hde.symm)

section Doubling

variable (K : PocketFaceSet D eps X lo hi) (f : X.toCombMap.Face)
  (j : Fin (X.faceBoundary f).darts.length) (hlen : 1 < (X.faceBoundary f).darts.length)
  (hf : f ≠ X.outerFace) (hs : f ∉ K.faces)
  (hsrc : FaceEdgeDoubling.dart X f j ∉ K.sourceArc.darts)

/-- **A good face stays good on its image across a doubling.** -/
theorem goodFace_faceImage_faceEdgeDoubling {g : X.toCombMap.Face} (hg : GoodFace X K.faces g) :
    GoodFace (FaceEdgeDoubling.diagram X f j hlen hf) (K.faceEdgeDoubling f j hlen hf hs hsrc).faces
      (FaceEdgeDoubling.faceImage X f j hlen g) := by
  refine ⟨fun h => ?_, fun C hC hCg => ?_, ?_⟩
  · have houter : (FaceEdgeDoubling.diagram X f j hlen hf).outerFace =
        FaceEdgeDoubling.faceImage X f j hlen X.outerFace :=
      (FaceEdgeDoubling.faceImage_of_ne X f j hlen hf.symm).symm
    exact hg.1 (FaceEdgeDoubling.faceImage_injective X f j hlen (h.trans houter))
  · obtain ⟨C₀, hC₀, hface⟩ := FaceEdgeDoubling.exists_relatorCell_of_mem_diagram X f j hlen hf hC
    exact hg.2.1 C₀ hC₀ (FaceEdgeDoubling.faceImage_injective X f j hlen (hface.symm.trans hCg))
  · rw [faceEdgeDoubling_faces, FaceEdgeDoubling.faceImage_mem_faceSet_iff X f j hlen hf hs]
    exact hg.2.2

/-- **A corner off the doubled dart keeps the image of its face.** -/
theorem faceOf_alpha_embed_of_ne_faceEdgeDoubling {v : X.toCombMap.Dart}
    (hv : X.toCombMap.alpha v ≠ FaceEdgeDoubling.dart X f j) :
    (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.faceOf
        ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha
          ((FaceEdgeDoubling.embedding X f j hlen hf).darts v)) =
      FaceEdgeDoubling.faceImage X f j hlen (X.toCombMap.faceOf (X.toCombMap.alpha v)) := by
  rw [(FaceEdgeDoubling.embedding X f j hlen hf).alpha]
  exact FaceEdgeDoubling.faceOf_diagram_embed_of_ne X f j hlen hf hv

end Doubling

section Thickening

variable (K : PocketFaceSet D eps X lo hi) (j : Fin (X.faceBoundary X.outerFace).darts.length)
  (hlen : 1 < (X.faceBoundary X.outerFace).darts.length)
  (htgt : X.toCombMap.alpha (FaceEdgeDoubling.dart X X.outerFace j) ∉ K.targetArc.darts)

/-- **A good face stays good on its image across a thickening.** -/
theorem goodFace_faceImage_outerSpurThickening {g : X.toCombMap.Face}
    (hg : GoodFace X K.faces g) :
    GoodFace (OuterSpurThickening.diagram X j hlen) (K.outerSpurThickening j hlen htgt).faces
      (FaceEdgeDoubling.faceImage X X.outerFace j hlen g) := by
  refine ⟨fun h => ?_, fun C hC hCg => ?_, ?_⟩
  · exact hg.1 (FaceEdgeDoubling.faceImage_injective X X.outerFace j hlen
      (h.trans (FaceEdgeDoubling.faceImage_self X X.outerFace j hlen).symm))
  · obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
    exact hg.2.1 C₀ hC₀ (FaceEdgeDoubling.faceImage_injective X X.outerFace j hlen hCg)
  · rw [outerSpurThickening_faces]
    intro h
    obtain ⟨g', hg', himg⟩ := Finset.mem_map.mp h
    exact hg.2.2 (FaceEdgeDoubling.faceImage_injective X X.outerFace j hlen himg ▸ hg')

/-- **A corner off the thickened dart keeps the image of its face.** -/
theorem faceOf_alpha_embed_of_ne_outerSpurThickening {v : X.toCombMap.Dart}
    (hv : X.toCombMap.alpha v ≠ FaceEdgeDoubling.dart X X.outerFace j) :
    (OuterSpurThickening.diagram X j hlen).toCombMap.faceOf
        ((OuterSpurThickening.diagram X j hlen).toCombMap.alpha
          ((OuterSpurThickening.embedding X j hlen).darts v)) =
      FaceEdgeDoubling.faceImage X X.outerFace j hlen (X.toCombMap.faceOf (X.toCombMap.alpha v)) := by
  rw [(OuterSpurThickening.embedding X j hlen).alpha]
  by_cases he : X.toCombMap.faceOf (X.toCombMap.alpha v) = X.outerFace
  · rw [he, FaceEdgeDoubling.faceImage_self]
    exact FaceEdgeDoubling.faceOf_embed_of_face_of_ne X X.outerFace j hlen he hv
  · exact FaceEdgeDoubling.faceOf_embed_of_face_ne X X.outerFace j hlen he

end Thickening

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerGood.GoodFace
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerGood.inputOfGood
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerGood.inputOfGood_avoids
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerGood.not_cell_of_length_le_one
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerGood.eq_of_faceOf_eq_of_length_le_one
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerGood.exists_dart_eq_of_face
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerGood.next_ne_self
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerGood.chordData_init
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerGood.ChordData.withY
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchCornerGood.ChordData.x_ne_d₀
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.sameCycle_of_chordData
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.mem_ne_next_of_chordData
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.goodFace_faceImage_faceEdgeDoubling
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faceOf_alpha_embed_of_ne_faceEdgeDoubling
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.goodFace_faceImage_outerSpurThickening
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faceOf_alpha_embed_of_ne_outerSpurThickening
