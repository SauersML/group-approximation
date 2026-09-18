import GroupApproximation.Manuscript.NonMF.Full.GL06d.CornerBasic
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarDouble
import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingFaces
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterSpur
import GroupApproximation.Meta.AxiomGuard

/-!
# Non-rose step: the corner digon at a non-monogon corner

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Let `z → σ z` be a corner of a pocket
`K`, with corner face `f = face (α z)` outside the face set and `σ z ≠ α z`.  Both corner darts
lie on the traversal of `f`, so `f` has at least two darts.  A corner dart `wd` off the arcs
(`exists_corner_dart_inner`, `exists_corner_dart_outer`) sits at a position `k` of `f`
(`exists_corner_index`).

* If `f` is inner, double the edge `wd` (`PocketFaceSet.faceEdgeDoubling`).
* If `f` is the exterior, thicken the outer spur at `wd` (`PocketFaceSet.outerSpurThickening`).

Both surgeries are the edge insertion `EdgeInsertion.toCombMap M a b`, and the new digon is
`[none, embed wd]`.  If `wd = α z`, the digon is the corner face at `z` itself; if `wd = σ z`,
the step `z → σ z` passes the new dart `some none`, whose reverse `none` lies on the digon
(`exists_digon_sector`).  The digon is not a face image, so it is a G-face; the only old dart on
it is `wd` (`eq_of_faceOf_embed_digon`); and G-faces other than `f` stay G-faces.  The arcs keep
their lengths and the carriers are mapped lists, so the arcs stay proper
(`cornerDigon_of_nonMonogon`).

## Manuscript status

Infrastructure for `thm:hull` (`non_mf_groups_exist.tex`; Hull's small cancellation theorem,
through Osin's Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL06d

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.OuterPinchIsolated
open GroupApproximation.GGT.VanKampen.OuterPinchCorners
open GroupApproximation.GGT.VanKampen.OuterPinchCornerFix
open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lo hi : ℕ}

variable (X : DiscDiagram.{u, w, v} W)

section Inner

variable (f : X.toCombMap.Face) (k : Fin (X.faceBoundary f).darts.length)
  (hlen : 1 < (X.faceBoundary f).darts.length)

/-- The two corners of a doubling are distinct (`thm:hull`). -/
theorem corners_ne' :
    EdgeInsertion.firstCorner X.toCombMap (FaceEdgeDoubling.rebased X f k) ≠
      EdgeInsertion.secondCorner X.toCombMap (FaceEdgeDoubling.rebased X f k)
        (FaceEdgeDoubling.second X f k hlen) :=
  EdgeInsertion.corners_ne X.toCombMap (FaceEdgeDoubling.rebased X f k)
    (FaceEdgeDoubling.second X f k hlen) Nat.one_pos

/-- An old dart other than the doubled one lies on the image of its face (`thm:hull`). -/
theorem faceOf_embed_of_ne' {w : X.toCombMap.Dart} (hw : w ≠ FaceEdgeDoubling.dart X f k) :
    (FaceEdgeDoubling.map X f k hlen).faceOf (EdgeInsertion.embed X.toCombMap w) =
      FaceEdgeDoubling.faceImage X f k hlen (X.toCombMap.faceOf w) := by
  by_cases hg : X.toCombMap.faceOf w = f
  · rw [hg, FaceEdgeDoubling.faceImage_self]
    exact FaceEdgeDoubling.faceOf_embed_of_face_of_ne X f k hlen hg hw
  · exact FaceEdgeDoubling.faceOf_embed_of_face_ne X f k hlen hg

/-- The only old dart on the digon is the doubled dart (`thm:hull`). -/
theorem eq_of_faceOf_embed_digon {w : X.toCombMap.Dart}
    (h : (FaceEdgeDoubling.map X f k hlen).faceOf (EdgeInsertion.embed X.toCombMap w) =
      FaceEdgeDoubling.digon X f k hlen) :
    w = FaceEdgeDoubling.dart X f k := by
  by_contra hw
  rw [faceOf_embed_of_ne' X f k hlen hw] at h
  exact FaceEdgeDoubling.faceImage_ne_digon X f k hlen _ h

/-- **The digon sits in the corner of `z`**: the old step `z → σ z` is `p` new steps through new
darts only, and the `m`-th corner face on the way is the digon (`thm:hull`). -/
theorem exists_digon_sector {z : X.toCombMap.Dart}
    (hdz : FaceEdgeDoubling.dart X f k = X.toCombMap.alpha z ∨
      FaceEdgeDoubling.dart X f k = X.toCombMap.sigma z) :
    ∃ p m : ℕ, m < p ∧
      ((FaceEdgeDoubling.map X f k hlen).sigma ^ p) (EdgeInsertion.embed X.toCombMap z) =
        EdgeInsertion.embed X.toCombMap (X.toCombMap.sigma z) ∧
      (∀ t, 0 < t → t < p → ∀ w, ((FaceEdgeDoubling.map X f k hlen).sigma ^ t)
        (EdgeInsertion.embed X.toCombMap z) ≠ EdgeInsertion.embed X.toCombMap w) ∧
      (FaceEdgeDoubling.map X f k hlen).faceOf ((FaceEdgeDoubling.map X f k hlen).alpha
        (((FaceEdgeDoubling.map X f k hlen).sigma ^ m) (EdgeInsertion.embed X.toCombMap z))) =
        FaceEdgeDoubling.digon X f k hlen := by
  rcases hdz with hα | hσ
  · obtain ⟨p, hp, hpz, hpmid⟩ :=
      EdgeInsertion.exists_sigma_step_lift (corners_ne' X f k hlen) z
    refine ⟨p, 0, hp, hpz, fun t ht htp w hw => ?_, ?_⟩
    · rcases hpmid t ht htp with h | h
      · exact absurd (h.symm.trans hw) (by simp [EdgeInsertion.embed])
      · exact absurd (h.symm.trans hw) (by simp [EdgeInsertion.embed])
    · rw [pow_zero, Equiv.Perm.one_apply]
      change (FaceEdgeDoubling.map X f k hlen).faceOf
        (EdgeInsertion.embed X.toCombMap (X.toCombMap.alpha z)) = _
      rw [← hα]
      exact FaceEdgeDoubling.faceOf_embed_dart_digon X f k hlen
  · have hσ' : X.toCombMap.sigma z =
        EdgeInsertion.firstCorner X.toCombMap (FaceEdgeDoubling.rebased X f k) := hσ.symm
    have h1 : (FaceEdgeDoubling.map X f k hlen).sigma (EdgeInsertion.embed X.toCombMap z) =
        some none := by
      rw [EdgeInsertion.sigma_embed_apply (corners_ne' X f k hlen) z, if_pos hσ']
    refine ⟨2, 1, Nat.one_lt_two, ?_, fun t ht ht2 w hw => ?_, ?_⟩
    · rw [pow_two, Equiv.Perm.mul_apply, h1]
      exact (GeodesicCollar.edgeInsertion_sigma_some_none (corners_ne' X f k hlen)).trans
        (congrArg (EdgeInsertion.embed X.toCombMap) hσ'.symm)
    · obtain rfl : t = 1 := by omega
      rw [pow_one, h1] at hw
      simp [EdgeInsertion.embed] at hw
    · rw [pow_one, h1]
      change (FaceEdgeDoubling.map X f k hlen).faceOf none = _
      exact FaceEdgeDoubling.faceOf_none_digon X f k hlen

/-- The digon of an inner doubling is a G-face (`thm:hull`). -/
theorem digon_isGFace_inner (hf : f ≠ X.outerFace) :
    IsGFaceOf (FaceEdgeDoubling.diagram X f k hlen hf) (FaceEdgeDoubling.digon X f k hlen) := by
  refine ⟨fun h => FaceEdgeDoubling.keep_ne_digon X f k hlen hf.symm h.symm, fun C hC h => ?_⟩
  obtain ⟨C₀, -, hC₀f⟩ := FaceEdgeDoubling.exists_relatorCell_of_mem_diagram X f k hlen hf hC
  exact FaceEdgeDoubling.faceImage_ne_digon X f k hlen C₀.face (hC₀f.symm.trans h)

/-- A G-face other than the doubled face stays a G-face (`thm:hull`). -/
theorem isGFace_transfer_inner (hf : f ≠ X.outerFace) (w : X.toCombMap.Dart)
    (hG : IsGFaceOf X (X.toCombMap.faceOf w)) (hwf : X.toCombMap.faceOf w ≠ f) :
    IsGFaceOf (FaceEdgeDoubling.diagram X f k hlen hf)
      ((FaceEdgeDoubling.map X f k hlen).faceOf (EdgeInsertion.embed X.toCombMap w)) := by
  refine isGFaceOf_congr (FaceEdgeDoubling.faceOf_embed_of_face_ne X f k hlen hwf) ⟨?_, ?_⟩
  · intro h
    exact hG.1 (FaceEdgeDoubling.faceImage_injective X f k hlen
      (h.trans (FaceEdgeDoubling.faceImage_of_ne X f k hlen hf.symm).symm))
  · intro C hC h
    obtain ⟨C₀, hC₀, hC₀f⟩ :=
      FaceEdgeDoubling.exists_relatorCell_of_mem_diagram X f k hlen hf hC
    exact hG.2 C₀ hC₀ (FaceEdgeDoubling.faceImage_injective X f k hlen (hC₀f.symm.trans h))

section Arcs

variable (K : PocketFaceSet D eps X lo hi) (hf : f ≠ X.outerFace) (hs : f ∉ K.faces)
  (hsrc : FaceEdgeDoubling.dart X f k ∉ K.sourceArc.darts)

/-- A proper source arc stays proper across an inner doubling (`thm:hull`). -/
theorem inner_source_proper (hprop : K.sourceArc.length < (cellDarts X K.source).length) :
    (K.faceEdgeDoubling f k hlen hf hs hsrc).sourceArc.length <
      (cellDarts (FaceEdgeDoubling.diagram X f k hlen hf)
        (K.faceEdgeDoubling f k hlen hf hs hsrc).source).length := by
  have h1 : (K.faceEdgeDoubling f k hlen hf hs hsrc).sourceArc.length = K.sourceArc.length :=
    CyclicArc.mapTo_length K.sourceArc _ (FaceEdgeDoubling.cellDarts_eq X f k hlen hf K.source)
  have h2 : (cellDarts (FaceEdgeDoubling.diagram X f k hlen hf)
      ((FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv K.source)).length =
        (cellDarts X K.source).length :=
    (congrArg List.length (FaceEdgeDoubling.cellDarts_eq X f k hlen hf K.source)).trans
      (List.length_map _)
  exact lt_of_eq_of_lt h1 (lt_of_lt_of_eq hprop h2.symm)

/-- A proper target arc stays proper across an inner doubling (`thm:hull`). -/
theorem inner_target_proper (hprop : K.targetArc.length < (outerDarts X).length) :
    (K.faceEdgeDoubling f k hlen hf hs hsrc).targetArc.length <
      (outerDarts (FaceEdgeDoubling.diagram X f k hlen hf)).length := by
  have h1 : (K.faceEdgeDoubling f k hlen hf hs hsrc).targetArc.length = K.targetArc.length :=
    CyclicArc.mapTo_length K.targetArc _
      ((FaceEdgeDoubling.embedding X f k hlen hf).outerDarts_eq hf)
  have h2 : (outerDarts (FaceEdgeDoubling.diagram X f k hlen hf)).length =
      (outerDarts X).length :=
    (congrArg List.length ((FaceEdgeDoubling.embedding X f k hlen hf).outerDarts_eq hf)).trans
      (List.length_map _)
  exact lt_of_eq_of_lt h1 (lt_of_lt_of_eq hprop h2.symm)

end Arcs

/-- **The corner digon from an inner doubling** (`thm:hull`). -/
theorem cornerDigon_faceEdgeDoubling (hlen : 1 < (X.faceBoundary f).darts.length)
    (K : PocketFaceSet D eps X lo hi) (hf : f ≠ X.outerFace)
    (hs : f ∉ K.faces) (hsrc : FaceEdgeDoubling.dart X f k ∉ K.sourceArc.darts)
    (z : X.toCombMap.Dart) (hinv : PocketInvariants K)
    (hfz : X.toCombMap.faceOf (X.toCombMap.alpha z) = f)
    (hdz : FaceEdgeDoubling.dart X f k = X.toCombMap.alpha z ∨
      FaceEdgeDoubling.dart X f k = X.toCombMap.sigma z) : CornerDigon K z := by
  obtain ⟨hlabel, hK, hsrcP, htgtP⟩ := hinv
  obtain ⟨p, m, hmp, hpz, hpmid, hface⟩ := exists_digon_sector X f k hlen hdz
  refine ⟨FaceEdgeDoubling.diagram X f k hlen hf, K.faceEdgeDoubling f k hlen hf hs hsrc,
    RotationRefinement.edgeInsertion (corners_ne' X f k hlen),
    ⟨FaceEdgeDoubling.oEquivalent X f k hlen hf⟩,
    ⟨FaceEdgeDoubling.label_letter X f k hlen hf hlabel,
      K.faceEdgeDoubling_closedWalk f k hlen hf hs hsrc hK,
      inner_source_proper X f k hlen K hf hs hsrc hsrcP,
      inner_target_proper X f k hlen K hf hs hsrc htgtP⟩,
    K.faceEdgeDoubling_repeatedVisits f k hlen hf hs hsrc,
    K.faceEdgeDoubling_boundary_cycle f k hlen hf hs hsrc,
    p, m, hmp, hpz, hpmid, isGFaceOf_congr hface (digon_isGFace_inner X f k hlen hf),
    fun w hw => ?_,
    fun w hG hne => isGFace_transfer_inner X f k hlen hf w hG (fun h => hne (h.trans hfz.symm))⟩
  have hw' := eq_of_faceOf_embed_digon X f k hlen (hw.trans hface)
  rcases hdz with h | h
  · exact Or.inl (hw'.trans h)
  · exact Or.inr (hw'.trans h)

end Inner

section Outer

variable (k : Fin (X.faceBoundary X.outerFace).darts.length)
  (hlen : 1 < (X.faceBoundary X.outerFace).darts.length)

/-- The digon of an outer thickening is a G-face (`thm:hull`). -/
theorem digon_isGFace_outer :
    IsGFaceOf (OuterSpurThickening.diagram X k hlen)
      (FaceEdgeDoubling.digon X X.outerFace k hlen) := by
  refine ⟨FaceEdgeDoubling.digon_ne_cellFace X X.outerFace k hlen, fun C hC h => ?_⟩
  have hC' : C ∈ X.relatorCells.map (OuterSpurThickening.spurCell X k hlen) := hC
  obtain ⟨C₀, -, hCeq⟩ := List.mem_map.mp hC'
  exact FaceEdgeDoubling.faceImage_ne_digon X X.outerFace k hlen C₀.face
    ((congrArg RelatorCell.face hCeq).trans h)

/-- Every G-face stays a G-face across an outer thickening (`thm:hull`). -/
theorem isGFace_transfer_outer (w : X.toCombMap.Dart) (hG : IsGFaceOf X (X.toCombMap.faceOf w)) :
    IsGFaceOf (OuterSpurThickening.diagram X k hlen)
      ((FaceEdgeDoubling.map X X.outerFace k hlen).faceOf
        (EdgeInsertion.embed X.toCombMap w)) := by
  refine isGFaceOf_congr (FaceEdgeDoubling.faceOf_embed_of_face_ne X X.outerFace k hlen hG.1)
    ⟨?_, ?_⟩
  · intro h
    exact hG.1 (FaceEdgeDoubling.faceImage_injective X X.outerFace k hlen
      (h.trans (FaceEdgeDoubling.faceImage_self X X.outerFace k hlen).symm))
  · intro C hC h
    have hC' : C ∈ X.relatorCells.map (OuterSpurThickening.spurCell X k hlen) := hC
    obtain ⟨C₀, hC₀, hCeq⟩ := List.mem_map.mp hC'
    exact hG.2 C₀ hC₀ (FaceEdgeDoubling.faceImage_injective X X.outerFace k hlen
      ((congrArg RelatorCell.face hCeq).trans h))

section Arcs

variable (K : PocketFaceSet D eps X lo hi)
  (htgt : X.toCombMap.alpha (FaceEdgeDoubling.dart X X.outerFace k) ∉ K.targetArc.darts)

/-- A proper source arc stays proper across an outer thickening (`thm:hull`). -/
theorem outer_source_proper (hprop : K.sourceArc.length < (cellDarts X K.source).length) :
    (K.outerSpurThickening k hlen htgt).sourceArc.length <
      (cellDarts (OuterSpurThickening.diagram X k hlen)
        (K.outerSpurThickening k hlen htgt).source).length := by
  have h2 : (cellDarts (OuterSpurThickening.diagram X k hlen)
      ((OuterSpurThickening.cellMap X k hlen).indexEquiv K.source)).length =
        (cellDarts X K.source).length :=
    (congrArg List.length (OuterSpurThickening.cellDarts_eq X k hlen K.source)).trans
      (List.length_map _)
  exact lt_of_eq_of_lt (K.outerSpurThickening_sourceArc_length k hlen htgt)
    (lt_of_lt_of_eq hprop h2.symm)

/-- A proper target arc stays proper across an outer thickening (`thm:hull`). -/
theorem outer_target_proper (hprop : K.targetArc.length < (outerDarts X).length) :
    (K.outerSpurThickening k hlen htgt).targetArc.length <
      (outerDarts (OuterSpurThickening.diagram X k hlen)).length := by
  have h2 : (outerDarts (OuterSpurThickening.diagram X k hlen)).length = (outerDarts X).length :=
    (congrArg List.length (OuterSpurThickening.outerDarts_eq X k hlen)).trans (List.length_map _)
  exact lt_of_eq_of_lt (K.outerSpurThickening_targetArc_length k hlen htgt)
    (lt_of_lt_of_eq hprop h2.symm)

end Arcs

/-- **The corner digon from an outer thickening** (`thm:hull`). -/
theorem cornerDigon_outerSpur (hlen : 1 < (X.faceBoundary X.outerFace).darts.length)
    (K : PocketFaceSet D eps X lo hi)
    (htgt : X.toCombMap.alpha (FaceEdgeDoubling.dart X X.outerFace k) ∉ K.targetArc.darts)
    (z : X.toCombMap.Dart) (hinv : PocketInvariants K)
    (hdz : FaceEdgeDoubling.dart X X.outerFace k = X.toCombMap.alpha z ∨
      FaceEdgeDoubling.dart X X.outerFace k = X.toCombMap.sigma z) : CornerDigon K z := by
  obtain ⟨hlabel, hK, hsrcP, htgtP⟩ := hinv
  obtain ⟨p, m, hmp, hpz, hpmid, hface⟩ := exists_digon_sector X X.outerFace k hlen hdz
  refine ⟨OuterSpurThickening.diagram X k hlen, K.outerSpurThickening k hlen htgt,
    RotationRefinement.edgeInsertion (corners_ne' X X.outerFace k hlen),
    ⟨OuterSpurThickening.oEquivalent X k hlen⟩,
    ⟨OuterSpurThickening.label_letter X k hlen hlabel,
      K.outerSpurThickening_closedWalk k hlen htgt hK,
      outer_source_proper X k hlen K htgt hsrcP,
      outer_target_proper X k hlen K htgt htgtP⟩,
    K.outerSpurThickening_repeatedVisits k hlen htgt,
    K.outerSpurThickening_boundary_cycle k hlen htgt,
    p, m, hmp, hpz, hpmid, isGFaceOf_congr hface (digon_isGFace_outer X k hlen),
    fun w hw => ?_, fun w hG _ => isGFace_transfer_outer X k hlen w hG⟩
  have hw' := eq_of_faceOf_embed_digon X X.outerFace k hlen (hw.trans hface)
  rcases hdz with h | h
  · exact Or.inl (hw'.trans h)
  · exact Or.inr (hw'.trans h)

end Outer

/-- A corner dart of a non-monogon corner face is a position of that face, which has at least two
darts (`thm:hull`). -/
theorem exists_corner_index {g : X.toCombMap.Face} {z wd : X.toCombMap.Dart}
    (hg : X.toCombMap.faceOf (X.toCombMap.alpha z) = g)
    (hmono : X.toCombMap.sigma z ≠ X.toCombMap.alpha z)
    (hwd : wd = X.toCombMap.alpha z ∨ wd = X.toCombMap.sigma z) :
    ∃ (_ : 1 < (X.faceBoundary g).darts.length) (k : Fin (X.faceBoundary g).darts.length),
      FaceEdgeDoubling.dart X g k = wd := by
  have hmemα : X.toCombMap.alpha z ∈ (X.faceBoundary g).darts :=
    ((X.faceBoundary g).mem_iff _).mpr hg
  have hmemσ : X.toCombMap.sigma z ∈ (X.faceBoundary g).darts :=
    ((X.faceBoundary g).mem_iff _).mpr ((faceOf_sigma_eq_alpha _ z).trans hg)
  have hmemwd : wd ∈ (X.faceBoundary g).darts := by
    rcases hwd with rfl | rfl
    · exact hmemα
    · exact hmemσ
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hmemwd
  exact ⟨one_lt_length_of_mem_ne hmemα hmemσ (Ne.symm hmono), k,
    (FaceEdgeDoubling.dart_eq_get X g k).trans hk⟩

/-- **A corner digon at a non-monogon corner** outside the face set (`thm:hull`). -/
theorem cornerDigon_of_nonMonogon (K : PocketFaceSet D eps X lo hi)
    (z : X.toCombMap.Dart) (hinv : PocketInvariants K)
    (hs : X.toCombMap.faceOf (X.toCombMap.alpha z) ∉ K.faces)
    (hone : ¬ ∃ h : X.toCombMap.alpha (X.toCombMap.sigma z) ∈ K.boundary.cycle,
      K.boundary.cycle.next _ h = z)
    (hmono : X.toCombMap.sigma z ≠ X.toCombMap.alpha z) : CornerDigon K z := by
  by_cases hfo : X.toCombMap.faceOf (X.toCombMap.alpha z) = X.outerFace
  · obtain ⟨wd, hwd, hwd1⟩ := exists_corner_dart_outer K hinv.2.2.2 hone
    obtain ⟨hlen, k, hdart⟩ := exists_corner_index X hfo hmono hwd
    exact cornerDigon_outerSpur X k hlen K (by rw [hdart]; exact hwd1) z hinv
      (Or.imp (fun h => hdart.trans h) (fun h => hdart.trans h) hwd)
  · obtain ⟨wd, hwd, hwd1⟩ := exists_corner_dart_inner K hinv.2.2.1 hone
    obtain ⟨hlen, k, hdart⟩ := exists_corner_index X rfl hmono hwd
    exact cornerDigon_faceEdgeDoubling X _ k hlen K hfo hs (by rw [hdart]; exact hwd1) z hinv
      rfl (Or.imp (fun h => hdart.trans h) (fun h => hdart.trans h) hwd)

end GroupApproximation.Full.GL06d

#audit_axioms GroupApproximation.Full.GL06d.corners_ne'
#audit_axioms GroupApproximation.Full.GL06d.faceOf_embed_of_ne'
#audit_axioms GroupApproximation.Full.GL06d.eq_of_faceOf_embed_digon
#audit_axioms GroupApproximation.Full.GL06d.exists_digon_sector
#audit_axioms GroupApproximation.Full.GL06d.digon_isGFace_inner
#audit_axioms GroupApproximation.Full.GL06d.isGFace_transfer_inner
#audit_axioms GroupApproximation.Full.GL06d.inner_source_proper
#audit_axioms GroupApproximation.Full.GL06d.inner_target_proper
#audit_axioms GroupApproximation.Full.GL06d.cornerDigon_faceEdgeDoubling
#audit_axioms GroupApproximation.Full.GL06d.digon_isGFace_outer
#audit_axioms GroupApproximation.Full.GL06d.isGFace_transfer_outer
#audit_axioms GroupApproximation.Full.GL06d.outer_source_proper
#audit_axioms GroupApproximation.Full.GL06d.outer_target_proper
#audit_axioms GroupApproximation.Full.GL06d.cornerDigon_outerSpur
#audit_axioms GroupApproximation.Full.GL06d.exists_corner_index
#audit_axioms GroupApproximation.Full.GL06d.cornerDigon_of_nonMonogon
