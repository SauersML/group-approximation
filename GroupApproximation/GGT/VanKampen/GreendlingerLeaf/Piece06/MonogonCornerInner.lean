import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCornerRefinement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCornerTransport
import GroupApproximation.GGT.VanKampen.SurgeryMonogonDoublingStrip
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: the corner digon at an inner monogon corner face

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  When `σ z = α z` the corner face
`f = face (α z)` is a monogon `[α z]` (`monogon_length`).  It is not a cell of the pocket, since
both arcs are proper (`cell_face_ne_of_proper`).  When `f` is not the exterior, doubling its only
dart (`MonogonDoubling.diagram`) is the edge insertion from the corner of `σ z = α z` to itself.
So `embed` is a rotation refinement (`RotationRefinement.sameCorner`) and the old step `z → σ z`
becomes three new steps (`p = 3`).  `α' (embed z) = embed (α z)` lies on the new digon
(`inner_face0`, `m = 0`).  That digon is a G-face (`inner_digon_isGFace`) whose only old dart is
`α z` (`eq_of_digon`).  Every other G-face stays a G-face (`inner_transfer`), and the pocket
transports (`MonogonCorner.transport`).  This proves `CornerDigon K z` (`cornerDigon_inner`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner

universe u w v

open Equiv

/-- A nonempty duplicate-free list all of whose members are one element has length one. -/
theorem length_eq_one_of_forall_eq {α : Type*} {l : List α} {x : α} (hne : l ≠ [])
    (hnd : l.Nodup) (hall : ∀ d ∈ l, d = x) : l.length = 1 := by
  rcases l with _ | ⟨d0, _ | ⟨d1, rest⟩⟩
  · exact absurd rfl hne
  · rfl
  · have h01 : d0 = d1 :=
      (hall d0 List.mem_cons_self).trans (hall d1 (List.mem_cons_of_mem _ List.mem_cons_self)).symm
    exact ((List.nodup_cons.mp hnd).1 (by rw [h01]; exact List.mem_cons_self)).elim

section Sequence

variable {M : CombMap.{v}}

/-- No old dart in the middle of the three new steps. -/
theorem sameCorner_mid {a z : M.Dart} (ha : M.sigma z = a) :
    ∀ t, 0 < t → t < 3 → ∀ w, ((EdgeInsertion.toCombMap M a a).sigma ^ t)
      (EdgeInsertion.embed M z) ≠ EdgeInsertion.embed M w := by
  intro t ht ht3 w hw
  rcases (by omega : t = 1 ∨ t = 2) with rfl | rfl
  · rw [sameCorner_sigma_one ha] at hw
    exact Option.noConfusion (Option.some.inj hw)
  · rw [sameCorner_sigma_two ha] at hw
    exact Option.noConfusion hw

end Sequence

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

/-- **A corner with `σ z = α z` has a monogon corner face.** -/
theorem monogon_length (X : DiscDiagram.{u, w, v} W) {z : X.toCombMap.Dart}
    (hσα : X.toCombMap.sigma z = X.toCombMap.alpha z) :
    (X.faceBoundary (X.toCombMap.faceOf (X.toCombMap.alpha z))).darts.length = 1 := by
  have hfix : Function.IsFixedPt X.toCombMap.facePerm (X.toCombMap.alpha z) := by
    change X.toCombMap.sigma (X.toCombMap.alpha (X.toCombMap.alpha z)) = X.toCombMap.alpha z
    rw [X.toCombMap.alpha_involutive z]
    exact hσα
  refine length_eq_one_of_forall_eq (x := X.toCombMap.alpha z) (X.faceBoundary _).nonempty
    (X.faceBoundary _).nodup (fun d hd => ?_)
  have hsame := (CombMap.faceOf_eq_iff X.toCombMap _ _).mp
    (((X.faceBoundary _).mem_iff d).mp hd).symm
  exact (hsame.eq_of_left hfix).symm

/-- A cell with a proper arc of positive length is not a monogon. -/
theorem cell_face_ne_of_proper (X : DiscDiagram.{u, w, v} W) {k : Fin X.rCellCount}
    {g : X.toCombMap.Face} (hg : (X.faceBoundary g).darts.length = 1) {n : ℕ} (hpos : 0 < n)
    (hlt : n < (Embedded.cellDarts X k).length) : (Embedded.cell X k).face ≠ g := by
  intro h
  subst h
  have h1 : (Embedded.cellDarts X k).length = 1 := hg
  omega

variable (X : DiscDiagram.{u, w, v} W) (f : X.toCombMap.Face) (hf : f ≠ X.outerFace)
  (hlen : (X.faceBoundary f).darts.length = 1)

theorem inner_hcell (k : Fin X.rCellCount) (hk : (Embedded.cell X k).face ≠ f) :
    (Embedded.cell (MonogonDoubling.diagram X f hf hlen)
        ((MonogonDoubling.cellMap X f hf hlen).indexEquiv k)).face =
      (MonogonDoubling.embedding X f hf hlen).faces (Embedded.cell X k).face := by
  rw [(MonogonDoubling.cellMap X f hf hlen).indexed_cell,
    (MonogonDoubling.cellMap X f hf hlen).face_eq]
  exact MonogonDoubling.faceImage_of_ne X f hk

theorem inner_hvert (x y : X.toCombMap.Dart) :
    (MonogonDoubling.diagram X f hf hlen).toCombMap.vertexOf
        ((MonogonDoubling.embedding X f hf hlen).darts x) =
      (MonogonDoubling.diagram X f hf hlen).toCombMap.vertexOf
        ((MonogonDoubling.embedding X f hf hlen).darts y) ↔
      X.toCombMap.vertexOf x = X.toCombMap.vertexOf y :=
  GeodesicCollar.edgeInsertion_vertexOf_embed_iff X.toCombMap
    (EdgeInsertion.firstCorner X.toCombMap (X.faceBoundary f))
    (EdgeInsertion.secondCorner X.toCombMap (X.faceBoundary f) (MonogonDoubling.zero X f)) x y

theorem inner_face0 {z : X.toCombMap.Dart} (hfz : X.toCombMap.faceOf (X.toCombMap.alpha z) = f) :
    (MonogonDoubling.diagram X f hf hlen).toCombMap.faceOf
        ((MonogonDoubling.diagram X f hf hlen).toCombMap.alpha
          (((MonogonDoubling.diagram X f hf hlen).toCombMap.sigma ^ 0)
            ((RotationRefinement.sameCorner (MonogonDoubling.dart X f)).map z))) =
      MonogonDoubling.digon X f := by
  rw [pow_zero, Perm.one_apply]
  change (MonogonDoubling.map X f).faceOf (EdgeInsertion.embed X.toCombMap (X.toCombMap.alpha z)) =
    MonogonDoubling.digon X f
  exact MonogonDoubling.faceOf_embed_of_face X f hfz

/-- **The digon of an inner monogon doubling is a G-face.** -/
theorem inner_digon_isGFace :
    CornerRefine.IsGFaceOf (MonogonDoubling.diagram X f hf hlen) (MonogonDoubling.digon X f) :=
  ⟨fun h => MonogonDoubling.keep_ne_digon X f hf.symm h.symm,
    MonogonDoubling.digon_not_cell X f hf hlen⟩

/-- The only old dart on the digon is the dart of the monogon. -/
theorem eq_of_digon (hlen : (X.faceBoundary f).darts.length = 1) {z w : X.toCombMap.Dart}
    (hfz : X.toCombMap.faceOf (X.toCombMap.alpha z) = f)
    (hw : (MonogonDoubling.map X f).faceOf (EdgeInsertion.embed X.toCombMap w) =
      MonogonDoubling.digon X f) : w = X.toCombMap.alpha z := by
  by_cases hwf : X.toCombMap.faceOf w = f
  · exact (MonogonDoubling.dart_eq_of_face X f hlen hwf).symm.trans
      (MonogonDoubling.dart_eq_of_face X f hlen hfz)
  · exact absurd ((MonogonDoubling.faceOf_embed_of_ne X f hwf).symm.trans hw)
      (MonogonDoubling.keep_ne_digon X f hwf)

/-- **A G-face other than the monogon stays a G-face.** -/
theorem inner_transfer (w : X.toCombMap.Dart) (hG : CornerRefine.IsGFaceOf X (X.toCombMap.faceOf w))
    (hwf : X.toCombMap.faceOf w ≠ f) :
    CornerRefine.IsGFaceOf (MonogonDoubling.diagram X f hf hlen)
      ((MonogonDoubling.map X f).faceOf (EdgeInsertion.embed X.toCombMap w)) := by
  refine CornerRefine.isGFaceOf_congr (MonogonDoubling.faceOf_embed_of_ne X f hwf)
    ⟨fun h => hG.1 (MonogonDoubling.keep_injective X f
      (h : MonogonDoubling.keep X f (X.toCombMap.faceOf w) = MonogonDoubling.keep X f X.outerFace)),
      fun C hC h => ?_⟩
  change C ∈ X.relatorCells.map (MonogonDoubling.cell X f hf) at hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
  have h' : MonogonDoubling.faceImage X f C₀.face =
      MonogonDoubling.faceImage X f (X.toCombMap.faceOf w) :=
    h.trans (MonogonDoubling.faceImage_of_ne X f hwf).symm
  exact hG.2 C₀ hC₀ (MonogonDoubling.faceImage_injective X f h')

/-- **The corner digon at an inner monogon corner face.** -/
theorem cornerDigon_inner {i j : Fin X.rCellCount} (K : CellPocketFaceSet D eps X i j)
    (z : X.toCombMap.Dart) (hinv : CornerRefine.PocketInvariants K)
    (hfz : X.toCombMap.faceOf (X.toCombMap.alpha z) = f) (hf : f ≠ X.outerFace)
    (hs : f ∉ K.faces) (hσα : X.toCombMap.sigma z = X.toCombMap.alpha z) :
    CornerRefine.CornerDigon K z := by
  obtain ⟨hlabel, hK, hij, hfirstP, hsecondP⟩ := hinv
  have hlen : (X.faceBoundary f).darts.length = 1 := by
    rw [← hfz]
    exact monogon_length X hσα
  have hσ : X.toCombMap.sigma z = MonogonDoubling.dart X f :=
    (MonogonDoubling.dart_eq_of_face X f hlen ((congrArg X.toCombMap.faceOf hσα).trans hfz)).symm
  have hi : (Embedded.cell X i).face ≠ f := cell_face_ne_of_proper X hlen K.firstArc_pos hfirstP
  have hj : (Embedded.cell X j).face ≠ f := cell_face_ne_of_proper X hlen K.secondArc_pos hsecondP
  refine ⟨MonogonDoubling.diagram X f hf hlen,
    (MonogonDoubling.cellMap X f hf hlen).indexEquiv i,
    (MonogonDoubling.cellMap X f hf hlen).indexEquiv j,
    transport (MonogonDoubling.embedding X f hf hlen) (MonogonDoubling.cellMap X f hf hlen).indexEquiv
      (inner_hcell X f hf hlen) K hs hi hj,
    RotationRefinement.sameCorner (MonogonDoubling.dart X f),
    ⟨MonogonDoubling.oEquivalent X f hf hlen⟩,
    ⟨MonogonDoubling.label_admissible X f hf hlen (symmetricLabelAlphabet D)
        (symmetricLabelAlphabet.symmetric D) hlabel,
      transport_closedWalk (MonogonDoubling.embedding X f hf hlen)
        (MonogonDoubling.cellMap X f hf hlen).indexEquiv (inner_hcell X f hf hlen) K hs hi hj
        (inner_hvert X f hf hlen) hK,
      fun h => hij ((MonogonDoubling.cellMap X f hf hlen).indexEquiv.injective h),
      transport_first_proper (MonogonDoubling.embedding X f hf hlen)
        (MonogonDoubling.cellMap X f hf hlen).indexEquiv (inner_hcell X f hf hlen) K hs hi hj
        hfirstP,
      transport_second_proper (MonogonDoubling.embedding X f hf hlen)
        (MonogonDoubling.cellMap X f hf hlen).indexEquiv (inner_hcell X f hf hlen) K hs hi hj
        hsecondP⟩,
    transport_repeatedVisits (MonogonDoubling.embedding X f hf hlen)
      (MonogonDoubling.cellMap X f hf hlen).indexEquiv (inner_hcell X f hf hlen) K hs hi hj
      (inner_hvert X f hf hlen),
    transport_boundary_cycle (MonogonDoubling.embedding X f hf hlen)
      (MonogonDoubling.cellMap X f hf hlen).indexEquiv (inner_hcell X f hf hlen) K hs hi hj,
    3, 0, by omega, sameCorner_sigma_three hσ, sameCorner_mid hσ,
    CornerRefine.isGFaceOf_congr (inner_face0 X f hf hlen hfz) (inner_digon_isGFace X f hf hlen),
    fun w hw => Or.inl (eq_of_digon X f hlen hfz (hw.trans (inner_face0 X f hf hlen hfz))),
    fun w hG hne => inner_transfer X f hf hlen w hG (fun h => hne (h.trans hfz.symm))⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.monogon_length
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.MonogonCorner.cornerDigon_inner
