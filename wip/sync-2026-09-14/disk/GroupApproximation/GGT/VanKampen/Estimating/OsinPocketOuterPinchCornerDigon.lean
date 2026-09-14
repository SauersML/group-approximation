import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPinchChordData
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketTouchCornerThickening
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterSpur
import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingFaces
import GroupApproximation.Meta.AxiomGuard

/-!
# Turning a corner of an outer pinch into a G-digon

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  The corner after a split dart `u` lies on the face of `alpha u`.  Doubling an
edge `w_j` of that face (`PocketFaceSet.faceEdgeDoubling`), or thickening an edge of the exterior
(`PocketFaceSet.outerSpurThickening`), inserts the new dart `some none` before `w_j` in the rotation
and closes a G-digon `none, w_j`.
* Option A, with `w_j = alpha u`: the corner dart stays `u`, and its corner is the digon.
* Option B, with `w_j = σ u`: the corner dart becomes `some none`, whose reversal `none` lies on the
  digon.
The digon is neither the exterior nor a relator face, and it lies off the image face set.  The chord
data carry over (`OuterPinchTransport.ChordData.embed`), with the corner dart moved in option B
(`ChordData.embed_moveX`, `embed_moveY`).

* `OuterPinchTransport.ChordData.embed_moveX`, `embed_moveY`: the chord data with a corner dart moved
  onto the new dart before `σ u`.
* `PocketFaceSet.chordData_faceEdgeDoubling`, `faceOf_alpha_embed_faceEdgeDoubling`,
  `faceOf_alpha_some_none_faceEdgeDoubling`, `digon_not_mem_faceEdgeDoubling`: across a doubling.
* `PocketFaceSet.chordData_outerSpurThickening`, `faceOf_alpha_embed_outerSpurThickening`,
  `faceOf_alpha_some_none_outerSpurThickening`, `digon_ne_outerFace_outerSpurThickening`,
  `digon_not_cell_outerSpurThickening`, `digon_not_mem_outerSpurThickening`: across a thickening.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides
open scoped Classical

namespace OuterPinchTransport

variable {M : CombMap.{u}}

/-- **Moving the x-corner onto the new dart before `σ x`.** -/
theorem ChordData.embed_moveX {c : List M.Dart} (hnodup : c.Nodup) {d₀ e₀ x y : M.Dart}
    (H : ChordData M c d₀ e₀ x y) {a b : M.Dart} (hab : a ≠ b) (hxa : M.sigma x = a) :
    ChordData (EdgeInsertion.toCombMap M a b) (c.map (EdgeInsertion.embed M))
      (EdgeInsertion.embed M d₀) (EdgeInsertion.embed M e₀) (some none)
      (EdgeInsertion.embed M y) := by
  have H' := H.embed hnodup hab
  refine { H' with run_x := ?_ }
  obtain ⟨m', hm', hkeep'⟩ := H'.run_x
  have hstep : ((EdgeInsertion.toCombMap M a b).sigma ^ (m' + 1)) (EdgeInsertion.embed M e₀) =
      some none := by
    rw [pow_succ', Equiv.Perm.mul_apply, hm', EdgeInsertion.sigma_embed_apply hab, if_pos hxa]
  refine ⟨m' + 1, hstep, fun t ht0 ht => ?_⟩
  rcases Nat.lt_or_ge t (m' + 1) with hlt | hge
  · exact hkeep' t ht0 (by omega)
  · obtain rfl : t = m' + 1 := by omega
    rw [hstep]
    exact EdgeInsertion.not_walkKeep_map_embed_some_none a b c

/-- **Moving the y-corner onto the new dart before `σ y`.** -/
theorem ChordData.embed_moveY {c : List M.Dart} (hnodup : c.Nodup) {d₀ e₀ x y : M.Dart}
    (H : ChordData M c d₀ e₀ x y) {a b : M.Dart} (hab : a ≠ b) (hya : M.sigma y = a) :
    ChordData (EdgeInsertion.toCombMap M a b) (c.map (EdgeInsertion.embed M))
      (EdgeInsertion.embed M d₀) (EdgeInsertion.embed M e₀) (EdgeInsertion.embed M x)
      (some none) := by
  have H' := H.embed hnodup hab
  refine { H' with run_y := ?_ }
  obtain ⟨q, hq0, hq, hkeep⟩ := H.run_y
  have hq1 : (M.sigma ^ (q - 1)) (M.sigma y) = M.alpha d₀ := by
    rw [← Equiv.Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ q)]
    exact hq
  have hkeep1 : ∀ t, 0 < t → t < q - 1 → ¬ walkKeep M c ((M.sigma ^ t) (M.sigma y)) := by
    intro t ht0 ht
    rw [← Equiv.Perm.mul_apply, ← pow_succ]
    exact hkeep (t + 1) (by omega) (by omega)
  obtain ⟨hq', hkeep'⟩ :=
    EdgeInsertion.nonKeepRunStrict_embed hab c (M.sigma y) (M.alpha d₀) hq1 hkeep1
  have hstart : (EdgeInsertion.toCombMap M a b).sigma (some none) =
      EdgeInsertion.embed M (M.sigma y) := by
    rw [GeodesicCollar.edgeInsertion_sigma_some_none hab, hya]
  refine ⟨EdgeInsertion.liftCount hab (M.sigma y) (q - 1) + 1, by omega, ?_, fun t ht0 ht => ?_⟩
  · rw [pow_succ, Equiv.Perm.mul_apply, hstart]
    exact hq'
  · have hsplit : ((EdgeInsertion.toCombMap M a b).sigma ^ t) (some none) =
        ((EdgeInsertion.toCombMap M a b).sigma ^ (t - 1)) (EdgeInsertion.embed M (M.sigma y)) := by
      rw [← hstart, ← Equiv.Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ t)]
    rw [hsplit]
    rcases Nat.eq_zero_or_pos (t - 1) with h0 | hpos
    · rw [h0, pow_zero, Equiv.Perm.one_apply, EdgeInsertion.walkKeep_map_embed_iff]
      have hq2 : 1 < q := by
        have := EdgeInsertion.pos_of_liftCount_pos hab (M.sigma y) (k := q - 1) (by omega)
        omega
      have h := hkeep 1 Nat.one_pos hq2
      rwa [pow_one] at h
    · exact hkeep' (t - 1) hpos (by omega)

end OuterPinchTransport

open OuterPinchTransport

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

section Doubling

variable (K : PocketFaceSet D eps X lo hi) (f : X.toCombMap.Face)
  (j : Fin (X.faceBoundary f).darts.length) (hlen : 1 < (X.faceBoundary f).darts.length)
  (hf : f ≠ X.outerFace) (hs : f ∉ K.faces)
  (hsrc : FaceEdgeDoubling.dart X f j ∉ K.sourceArc.darts)

/-- **The chord data across a doubling.** -/
theorem chordData_faceEdgeDoubling {d₀ e₀ x y : X.toCombMap.Dart}
    (H : ChordData X.toCombMap K.boundary.cycle d₀ e₀ x y) :
    ChordData (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap
      (K.faceEdgeDoubling f j hlen hf hs hsrc).boundary.cycle
      ((FaceEdgeDoubling.embedding X f j hlen hf).darts d₀)
      ((FaceEdgeDoubling.embedding X f j hlen hf).darts e₀)
      ((FaceEdgeDoubling.embedding X f j hlen hf).darts x)
      ((FaceEdgeDoubling.embedding X f j hlen hf).darts y) :=
  H.embed K.boundary.cycle_nodup (EdgeInsertion.corners_ne X.toCombMap
    (FaceEdgeDoubling.rebased X f j) (FaceEdgeDoubling.second X f j hlen) Nat.one_pos)

/-- **The chord data across a doubling at `σ x`**, with the x-corner moved onto the new dart. -/
theorem chordData_faceEdgeDoubling_moveX {d₀ e₀ x y : X.toCombMap.Dart}
    (H : ChordData X.toCombMap K.boundary.cycle d₀ e₀ x y)
    (hj : FaceEdgeDoubling.dart X f j = X.toCombMap.sigma x) :
    ChordData (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap
      (K.faceEdgeDoubling f j hlen hf hs hsrc).boundary.cycle
      ((FaceEdgeDoubling.embedding X f j hlen hf).darts d₀)
      ((FaceEdgeDoubling.embedding X f j hlen hf).darts e₀) (some none)
      ((FaceEdgeDoubling.embedding X f j hlen hf).darts y) :=
  H.embed_moveX K.boundary.cycle_nodup (EdgeInsertion.corners_ne X.toCombMap
    (FaceEdgeDoubling.rebased X f j) (FaceEdgeDoubling.second X f j hlen) Nat.one_pos) hj.symm

/-- **The chord data across a doubling at `σ y`**, with the y-corner moved onto the new dart. -/
theorem chordData_faceEdgeDoubling_moveY {d₀ e₀ x y : X.toCombMap.Dart}
    (H : ChordData X.toCombMap K.boundary.cycle d₀ e₀ x y)
    (hj : FaceEdgeDoubling.dart X f j = X.toCombMap.sigma y) :
    ChordData (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap
      (K.faceEdgeDoubling f j hlen hf hs hsrc).boundary.cycle
      ((FaceEdgeDoubling.embedding X f j hlen hf).darts d₀)
      ((FaceEdgeDoubling.embedding X f j hlen hf).darts e₀)
      ((FaceEdgeDoubling.embedding X f j hlen hf).darts x) (some none) :=
  H.embed_moveY K.boundary.cycle_nodup (EdgeInsertion.corners_ne X.toCombMap
    (FaceEdgeDoubling.rebased X f j) (FaceEdgeDoubling.second X f j hlen) Nat.one_pos) hj.symm

/-- **Option A: the corner of the doubled reversal is the digon.** -/
theorem faceOf_alpha_embed_faceEdgeDoubling {u : X.toCombMap.Dart}
    (hj : FaceEdgeDoubling.dart X f j = X.toCombMap.alpha u) :
    (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.faceOf
        ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha
          ((FaceEdgeDoubling.embedding X f j hlen hf).darts u)) =
      FaceEdgeDoubling.digon X f j hlen := by
  rw [(FaceEdgeDoubling.embedding X f j hlen hf).alpha, ← hj]
  exact FaceEdgeDoubling.faceOf_diagram_embed_dart X f j hlen hf

/-- **Option B: the corner of the new dart is the digon.** -/
theorem faceOf_alpha_some_none_faceEdgeDoubling :
    (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.faceOf
        ((FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.alpha (some none)) =
      FaceEdgeDoubling.digon X f j hlen :=
  FaceEdgeDoubling.faceOf_none_digon X f j hlen

/-- **The digon lies off the image face set.** -/
theorem digon_not_mem_faceEdgeDoubling :
    FaceEdgeDoubling.digon X f j hlen ∉ (K.faceEdgeDoubling f j hlen hf hs hsrc).faces := by
  rw [faceEdgeDoubling_faces]
  intro h
  obtain ⟨g, hg, hkeep⟩ := Finset.mem_map.mp h
  exact FaceEdgeDoubling.keep_ne_digon X f j hlen (fun hgf => hs (hgf ▸ hg)) hkeep

end Doubling

section Thickening

variable (K : PocketFaceSet D eps X lo hi) (j : Fin (X.faceBoundary X.outerFace).darts.length)
  (hlen : 1 < (X.faceBoundary X.outerFace).darts.length)
  (htgt : X.toCombMap.alpha (FaceEdgeDoubling.dart X X.outerFace j) ∉ K.targetArc.darts)

/-- **The chord data across a thickening.** -/
theorem chordData_outerSpurThickening {d₀ e₀ x y : X.toCombMap.Dart}
    (H : ChordData X.toCombMap K.boundary.cycle d₀ e₀ x y) :
    ChordData (OuterSpurThickening.diagram X j hlen).toCombMap
      (K.outerSpurThickening j hlen htgt).boundary.cycle
      ((OuterSpurThickening.embedding X j hlen).darts d₀)
      ((OuterSpurThickening.embedding X j hlen).darts e₀)
      ((OuterSpurThickening.embedding X j hlen).darts x)
      ((OuterSpurThickening.embedding X j hlen).darts y) :=
  H.embed K.boundary.cycle_nodup (EdgeInsertion.corners_ne X.toCombMap
    (FaceEdgeDoubling.rebased X X.outerFace j) (FaceEdgeDoubling.second X X.outerFace j hlen)
    Nat.one_pos)

/-- **The chord data across a thickening at `σ x`**, with the x-corner moved onto the new dart. -/
theorem chordData_outerSpurThickening_moveX {d₀ e₀ x y : X.toCombMap.Dart}
    (H : ChordData X.toCombMap K.boundary.cycle d₀ e₀ x y)
    (hj : FaceEdgeDoubling.dart X X.outerFace j = X.toCombMap.sigma x) :
    ChordData (OuterSpurThickening.diagram X j hlen).toCombMap
      (K.outerSpurThickening j hlen htgt).boundary.cycle
      ((OuterSpurThickening.embedding X j hlen).darts d₀)
      ((OuterSpurThickening.embedding X j hlen).darts e₀) (some none)
      ((OuterSpurThickening.embedding X j hlen).darts y) :=
  H.embed_moveX K.boundary.cycle_nodup (EdgeInsertion.corners_ne X.toCombMap
    (FaceEdgeDoubling.rebased X X.outerFace j) (FaceEdgeDoubling.second X X.outerFace j hlen)
    Nat.one_pos) hj.symm

/-- **The chord data across a thickening at `σ y`**, with the y-corner moved onto the new dart. -/
theorem chordData_outerSpurThickening_moveY {d₀ e₀ x y : X.toCombMap.Dart}
    (H : ChordData X.toCombMap K.boundary.cycle d₀ e₀ x y)
    (hj : FaceEdgeDoubling.dart X X.outerFace j = X.toCombMap.sigma y) :
    ChordData (OuterSpurThickening.diagram X j hlen).toCombMap
      (K.outerSpurThickening j hlen htgt).boundary.cycle
      ((OuterSpurThickening.embedding X j hlen).darts d₀)
      ((OuterSpurThickening.embedding X j hlen).darts e₀)
      ((OuterSpurThickening.embedding X j hlen).darts x) (some none) :=
  H.embed_moveY K.boundary.cycle_nodup (EdgeInsertion.corners_ne X.toCombMap
    (FaceEdgeDoubling.rebased X X.outerFace j) (FaceEdgeDoubling.second X X.outerFace j hlen)
    Nat.one_pos) hj.symm

/-- **Option A on the exterior: the corner of the thickened reversal is the digon.** -/
theorem faceOf_alpha_embed_outerSpurThickening {u : X.toCombMap.Dart}
    (hj : FaceEdgeDoubling.dart X X.outerFace j = X.toCombMap.alpha u) :
    (OuterSpurThickening.diagram X j hlen).toCombMap.faceOf
        ((OuterSpurThickening.diagram X j hlen).toCombMap.alpha
          ((OuterSpurThickening.embedding X j hlen).darts u)) =
      FaceEdgeDoubling.digon X X.outerFace j hlen := by
  rw [(OuterSpurThickening.embedding X j hlen).alpha, ← hj]
  exact FaceEdgeDoubling.faceOf_embed_dart_digon X X.outerFace j hlen

/-- **Option B on the exterior: the corner of the new dart is the digon.** -/
theorem faceOf_alpha_some_none_outerSpurThickening :
    (OuterSpurThickening.diagram X j hlen).toCombMap.faceOf
        ((OuterSpurThickening.diagram X j hlen).toCombMap.alpha (some none)) =
      FaceEdgeDoubling.digon X X.outerFace j hlen :=
  FaceEdgeDoubling.faceOf_none_digon X X.outerFace j hlen

/-- **The digon is not the exterior of the thickened diagram.** -/
theorem digon_ne_outerFace_outerSpurThickening :
    FaceEdgeDoubling.digon X X.outerFace j hlen ≠ (OuterSpurThickening.diagram X j hlen).outerFace :=
  FaceEdgeDoubling.digon_ne_cellFace X X.outerFace j hlen

/-- **The digon is not a relator face of the thickened diagram.** -/
theorem digon_not_cell_outerSpurThickening :
    ∀ C ∈ (OuterSpurThickening.diagram X j hlen).relatorCells,
      C.face ≠ FaceEdgeDoubling.digon X X.outerFace j hlen := by
  intro C hC
  obtain ⟨C₀, -, rfl⟩ := List.mem_map.mp hC
  exact FaceEdgeDoubling.faceImage_ne_digon X X.outerFace j hlen C₀.face

/-- **The digon lies off the image face set of the thickening.** -/
theorem digon_not_mem_outerSpurThickening :
    FaceEdgeDoubling.digon X X.outerFace j hlen ∉ (K.outerSpurThickening j hlen htgt).faces := by
  rw [outerSpurThickening_faces]
  intro h
  obtain ⟨g, -, hg⟩ := Finset.mem_map.mp h
  exact FaceEdgeDoubling.faceImage_ne_digon X X.outerFace j hlen g hg

end Thickening

end PocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchTransport.ChordData.embed_moveX
#audit_axioms GroupApproximation.GGT.VanKampen.OuterPinchTransport.ChordData.embed_moveY
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.chordData_faceEdgeDoubling
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.chordData_faceEdgeDoubling_moveX
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.chordData_faceEdgeDoubling_moveY
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faceOf_alpha_embed_faceEdgeDoubling
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faceOf_alpha_some_none_faceEdgeDoubling
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.digon_not_mem_faceEdgeDoubling
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.chordData_outerSpurThickening
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.chordData_outerSpurThickening_moveX
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.chordData_outerSpurThickening_moveY
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faceOf_alpha_embed_outerSpurThickening
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.faceOf_alpha_some_none_outerSpurThickening
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.digon_ne_outerFace_outerSpurThickening
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.digon_not_cell_outerSpurThickening
#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.digon_not_mem_outerSpurThickening
