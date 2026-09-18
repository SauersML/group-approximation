import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellOuterSpur
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoublingFirstTurns
import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingFaces
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: the corner refinement at a bad corner (part 2, one corner digon)

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Step (2) of `Piece06/CornerRefine`: at a
corner `z → σ z` of the pocket whose corner face `f = face (α z)` is outside the face set and not a
monogon (`σ z ≠ α z`), one of the two corner darts `α z`, `σ z` lies on neither arc
(`exists_corner_dart`).  Doubling that dart `w_k` of `f` (`FaceEdgeDoubling.diagram`, or
`OuterSpurThickening.diagram` when `f` is the exterior) is the edge insertion at the corners
`w_k`, `w_{k+1}`, so it is a rotation refinement (`RotationRefinement.edgeInsertion`).

* When `w_k = α z`, the new dart `some none` sits just before `w_{k+1} = σ z`, the old successor
  of `z` stays in place (`m = 0`), and `α' (embed z) = embed (α z)` lies on the digon.
* When `w_k = σ z`, `σ' (embed z) = some none`, `σ' (some none) = embed (σ z)` (`p = 2`), and
  `α' (some none) = none` lies on the digon (`m = 1`).

The digon is a G-face (`digon_isGFace_inner`, `digon_isGFace_outer`); its only old darts are
`w_k` (`eq_of_faceOf_embed_digon`); every G-face other than `f` stays a G-face
(`isGFace_transfer_inner`, `isGFace_transfer_outer`).  This is `CornerDigon K z`
(`cornerDigon_of_nonMonogon`); together with the isolated `MonogonCornerStatement` it covers every
corner (`cornerDigon_of_monogonCorner`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated Equiv
open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}

variable (X : DiscDiagram.{u, w, v} W)

section Inner

variable (f : X.toCombMap.Face) (k : Fin (X.faceBoundary f).darts.length)
  (hlen : 1 < (X.faceBoundary f).darts.length)

/-- The two corners of the doubling are distinct. -/
theorem corners_ne' :
    EdgeInsertion.firstCorner X.toCombMap (FaceEdgeDoubling.rebased X f k) ≠
      EdgeInsertion.secondCorner X.toCombMap (FaceEdgeDoubling.rebased X f k)
        (FaceEdgeDoubling.second X f k hlen) :=
  EdgeInsertion.corners_ne X.toCombMap (FaceEdgeDoubling.rebased X f k)
    (FaceEdgeDoubling.second X f k hlen) Nat.one_pos

/-- An old dart other than the doubled one lies on the image of its face. -/
theorem faceOf_embed_of_ne' {w : X.toCombMap.Dart} (hw : w ≠ FaceEdgeDoubling.dart X f k) :
    (FaceEdgeDoubling.map X f k hlen).faceOf (EdgeInsertion.embed X.toCombMap w) =
      FaceEdgeDoubling.faceImage X f k hlen (X.toCombMap.faceOf w) := by
  by_cases hg : X.toCombMap.faceOf w = f
  · rw [hg, FaceEdgeDoubling.faceImage_self]
    exact FaceEdgeDoubling.faceOf_embed_of_face_of_ne X f k hlen hg hw
  · exact FaceEdgeDoubling.faceOf_embed_of_face_ne X f k hlen hg

/-- The only old dart on the digon is the doubled dart. -/
theorem eq_of_faceOf_embed_digon {w : X.toCombMap.Dart}
    (h : (FaceEdgeDoubling.map X f k hlen).faceOf (EdgeInsertion.embed X.toCombMap w) =
      FaceEdgeDoubling.digon X f k hlen) :
    w = FaceEdgeDoubling.dart X f k := by
  by_contra hw
  rw [faceOf_embed_of_ne' X f k hlen hw] at h
  exact FaceEdgeDoubling.faceImage_ne_digon X f k hlen _ h

/-- **The digon sits in the corner of `z`**: the old step `z → σ z` is `p` new steps past new darts
only, and the `m`-th corner face on the way is the digon. -/
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
  · obtain ⟨p, hp, hpz, hpmid⟩ := EdgeInsertion.exists_sigma_step_lift (corners_ne' X f k hlen) z
    refine ⟨p, 0, hp, hpz, fun t ht htp w hw => ?_, ?_⟩
    · rcases hpmid t ht htp with h | h
      · exact Option.noConfusion (h.symm.trans hw)
      · exact Option.noConfusion (Option.some.inj (h.symm.trans hw))
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
      exact Option.noConfusion (Option.some.inj hw)
    · rw [pow_one, h1]
      change (FaceEdgeDoubling.map X f k hlen).faceOf none = _
      exact FaceEdgeDoubling.faceOf_none_digon X f k hlen

/-- The digon of an inner doubling is a G-face. -/
theorem digon_isGFace_inner (hf : f ≠ X.outerFace) :
    IsGFaceOf (FaceEdgeDoubling.diagram X f k hlen hf) (FaceEdgeDoubling.digon X f k hlen) := by
  refine ⟨fun h => FaceEdgeDoubling.keep_ne_digon X f k hlen hf.symm h.symm, fun C hC h => ?_⟩
  obtain ⟨C₀, -, hC₀f⟩ := FaceEdgeDoubling.exists_relatorCell_of_mem_diagram X f k hlen hf hC
  exact FaceEdgeDoubling.faceImage_ne_digon X f k hlen C₀.face (hC₀f.symm.trans h)

/-- A G-face other than the doubled face stays a G-face. -/
theorem isGFace_transfer_inner (hf : f ≠ X.outerFace) (w : X.toCombMap.Dart)
    (hG : IsGFaceOf X (X.toCombMap.faceOf w)) (hwf : X.toCombMap.faceOf w ≠ f) :
    IsGFaceOf (FaceEdgeDoubling.diagram X f k hlen hf)
      ((FaceEdgeDoubling.map X f k hlen).faceOf (EdgeInsertion.embed X.toCombMap w)) := by
  refine isGFaceOf_congr (FaceEdgeDoubling.faceOf_embed_of_face_ne X f k hlen hwf) ⟨?_, ?_⟩
  · intro h
    exact hG.1 (FaceEdgeDoubling.faceImage_injective X f k hlen
      (h.trans (FaceEdgeDoubling.faceImage_of_ne X f k hlen hf.symm).symm))
  · intro C hC h
    obtain ⟨C₀, hC₀, hC₀f⟩ := FaceEdgeDoubling.exists_relatorCell_of_mem_diagram X f k hlen hf hC
    exact hG.2 C₀ hC₀ (FaceEdgeDoubling.faceImage_injective X f k hlen (hC₀f.symm.trans h))

variable {i j : Fin X.rCellCount} (K : CellPocketFaceSet D eps X i j) (hf : f ≠ X.outerFace)
  (hs : f ∉ K.faces) (hfirst : FaceEdgeDoubling.dart X f k ∉ K.firstArc.darts)
  (hsecond : FaceEdgeDoubling.dart X f k ∉ K.secondArc.darts)

theorem inner_first_proper (hprop : K.firstArc.length < (cellDarts X i).length) :
    (K.faceEdgeDoubling f k hlen hf hs hfirst hsecond).firstArc.length <
      (cellDarts (FaceEdgeDoubling.diagram X f k hlen hf)
        ((FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv i)).length := by
  have h1 : (K.faceEdgeDoubling f k hlen hf hs hfirst hsecond).firstArc.length =
      K.firstArc.length :=
    CyclicArc.mapTo_length K.firstArc _ (FaceEdgeDoubling.cellDarts_eq X f k hlen hf i)
  have h2 : (cellDarts (FaceEdgeDoubling.diagram X f k hlen hf)
      ((FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv i)).length = (cellDarts X i).length :=
    (congrArg List.length (FaceEdgeDoubling.cellDarts_eq X f k hlen hf i)).trans (List.length_map _)
  exact lt_of_eq_of_lt h1 (lt_of_lt_of_eq hprop h2.symm)

theorem inner_second_proper (hprop : K.secondArc.length < (cellDarts X j).length) :
    (K.faceEdgeDoubling f k hlen hf hs hfirst hsecond).secondArc.length <
      (cellDarts (FaceEdgeDoubling.diagram X f k hlen hf)
        ((FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv j)).length := by
  have h1 : (K.faceEdgeDoubling f k hlen hf hs hfirst hsecond).secondArc.length =
      K.secondArc.length :=
    CyclicArc.mapTo_length K.secondArc _ (FaceEdgeDoubling.cellDarts_eq X f k hlen hf j)
  have h2 : (cellDarts (FaceEdgeDoubling.diagram X f k hlen hf)
      ((FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv j)).length = (cellDarts X j).length :=
    (congrArg List.length (FaceEdgeDoubling.cellDarts_eq X f k hlen hf j)).trans (List.length_map _)
  exact lt_of_eq_of_lt h1 (lt_of_lt_of_eq hprop h2.symm)

include hlen hf hs hfirst hsecond in
/-- **The corner digon from an inner doubling.** -/
theorem cornerDigon_faceEdgeDoubling (z : X.toCombMap.Dart) (hinv : PocketInvariants K)
    (hfz : X.toCombMap.faceOf (X.toCombMap.alpha z) = f)
    (hdz : FaceEdgeDoubling.dart X f k = X.toCombMap.alpha z ∨
      FaceEdgeDoubling.dart X f k = X.toCombMap.sigma z) : CornerDigon K z := by
  obtain ⟨hlabel, hK, hij, hfirstP, hsecondP⟩ := hinv
  obtain ⟨p, m, hmp, hpz, hpmid, hface⟩ := exists_digon_sector X f k hlen hdz
  refine ⟨FaceEdgeDoubling.diagram X f k hlen hf,
    (FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv i,
    (FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv j,
    K.faceEdgeDoubling f k hlen hf hs hfirst hsecond,
    RotationRefinement.edgeInsertion (corners_ne' X f k hlen),
    ⟨FaceEdgeDoubling.oEquivalent X f k hlen hf⟩,
    ⟨FaceEdgeDoubling.label_letter X f k hlen hf hlabel,
      K.faceEdgeDoubling_closedWalk f k hlen hf hs hfirst hsecond hK,
      fun h => hij ((FaceEdgeDoubling.cellMap X f k hlen hf).indexEquiv.injective h),
      inner_first_proper X f k hlen K hf hs hfirst hsecond hfirstP,
      inner_second_proper X f k hlen K hf hs hfirst hsecond hsecondP⟩,
    K.faceEdgeDoubling_repeatedVisits f k hlen hf hs hfirst hsecond,
    K.faceEdgeDoubling_boundary_cycle f k hlen hf hs hfirst hsecond,
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

/-- The digon of an outer thickening is a G-face. -/
theorem digon_isGFace_outer :
    IsGFaceOf (OuterSpurThickening.diagram X k hlen)
      (FaceEdgeDoubling.digon X X.outerFace k hlen) := by
  refine ⟨FaceEdgeDoubling.digon_ne_cellFace X X.outerFace k hlen, fun C hC h => ?_⟩
  have hC' : C ∈ X.relatorCells.map (OuterSpurThickening.spurCell X k hlen) := hC
  obtain ⟨C₀, -, hCeq⟩ := List.mem_map.mp hC'
  exact FaceEdgeDoubling.faceImage_ne_digon X X.outerFace k hlen C₀.face
    ((congrArg RelatorCell.face hCeq).trans h)

/-- Every G-face stays a G-face across an outer thickening. -/
theorem isGFace_transfer_outer (w : X.toCombMap.Dart) (hG : IsGFaceOf X (X.toCombMap.faceOf w)) :
    IsGFaceOf (OuterSpurThickening.diagram X k hlen)
      ((FaceEdgeDoubling.map X X.outerFace k hlen).faceOf (EdgeInsertion.embed X.toCombMap w)) := by
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

include hlen in
/-- **The corner digon from an outer thickening.** -/
theorem cornerDigon_outerSpur {i j : Fin X.rCellCount} (K : CellPocketFaceSet D eps X i j)
    (z : X.toCombMap.Dart) (hinv : PocketInvariants K)
    (hdz : FaceEdgeDoubling.dart X X.outerFace k = X.toCombMap.alpha z ∨
      FaceEdgeDoubling.dart X X.outerFace k = X.toCombMap.sigma z) : CornerDigon K z := by
  obtain ⟨hlabel, hK, hij, hfirstP, hsecondP⟩ := hinv
  obtain ⟨p, m, hmp, hpz, hpmid, hface⟩ := exists_digon_sector X X.outerFace k hlen hdz
  refine ⟨OuterSpurThickening.diagram X k hlen,
    (OuterSpurThickening.cellMap X k hlen).indexEquiv i,
    (OuterSpurThickening.cellMap X k hlen).indexEquiv j,
    K.outerSpurThickening k hlen,
    RotationRefinement.edgeInsertion (corners_ne' X X.outerFace k hlen),
    ⟨OuterSpurThickening.oEquivalent X k hlen⟩,
    ⟨OuterSpurThickening.label_letter X k hlen hlabel,
      K.outerSpurThickening_closedWalk k hlen hK,
      fun h => hij ((OuterSpurThickening.cellMap X k hlen).indexEquiv.injective h),
      K.outerSpurThickening_first_proper k hlen hfirstP,
      K.outerSpurThickening_second_proper k hlen hsecondP⟩,
    K.outerSpurThickening_repeatedVisits k hlen,
    K.outerSpurThickening_boundary_cycle k hlen,
    p, m, hmp, hpz, hpmid, isGFaceOf_congr hface (digon_isGFace_outer X k hlen),
    fun w hw => ?_, fun w hG _ => isGFace_transfer_outer X k hlen w hG⟩
  have hw' := eq_of_faceOf_embed_digon X X.outerFace k hlen (hw.trans hface)
  rcases hdz with h | h
  · exact Or.inl (hw'.trans h)
  · exact Or.inr (hw'.trans h)

end Outer

/-- A corner dart of a non-monogon corner face is a position of that face, which has two darts. -/
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

/-- **A corner digon at a non-monogon corner** outside the face set. -/
theorem cornerDigon_of_nonMonogon {i j : Fin X.rCellCount} (K : CellPocketFaceSet D eps X i j)
    (z : X.toCombMap.Dart) (hinv : PocketInvariants K)
    (hs : X.toCombMap.faceOf (X.toCombMap.alpha z) ∉ K.faces)
    (hone : ¬ ∃ h : X.toCombMap.alpha (X.toCombMap.sigma z) ∈ K.boundary.cycle,
      K.boundary.cycle.next _ h = z)
    (hmono : X.toCombMap.sigma z ≠ X.toCombMap.alpha z) : CornerDigon K z := by
  obtain ⟨wd, hwd, hwd1, hwd2⟩ :=
    exists_corner_dart K hinv.2.2.1 hinv.2.2.2.1 hinv.2.2.2.2 hone
  by_cases hfo : X.toCombMap.faceOf (X.toCombMap.alpha z) = X.outerFace
  · obtain ⟨hlen, k, hdart⟩ := exists_corner_index X hfo hmono hwd
    exact cornerDigon_outerSpur X k hlen K z hinv
      (Or.imp (fun h => hdart.trans h) (fun h => hdart.trans h) hwd)
  · obtain ⟨hlen, k, hdart⟩ := exists_corner_index X rfl hmono hwd
    exact cornerDigon_faceEdgeDoubling X _ k hlen K hfo hs (by rw [hdart]; exact hwd1)
      (by rw [hdart]; exact hwd2) z hinv rfl
      (Or.imp (fun h => hdart.trans h) (fun h => hdart.trans h) hwd)

/-- **A corner digon at every corner**, from the isolated monogon case. -/
theorem cornerDigon_of_monogonCorner (hmono : MonogonCornerStatement.{u, w, v})
    {i j : Fin X.rCellCount} (K : CellPocketFaceSet D eps X i j) (z : X.toCombMap.Dart)
    (hinv : PocketInvariants K) (hs : X.toCombMap.faceOf (X.toCombMap.alpha z) ∉ K.faces)
    (hone : ¬ ∃ h : X.toCombMap.alpha (X.toCombMap.sigma z) ∈ K.boundary.cycle,
      K.boundary.cycle.next _ h = z) : CornerDigon K z := by
  by_cases h : X.toCombMap.sigma z = X.toCombMap.alpha z
  · exact hmono K z hinv hs hone h
  · exact cornerDigon_of_nonMonogon X K z hinv hs hone h

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.corners_ne'
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.faceOf_embed_of_ne'
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.eq_of_faceOf_embed_digon
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.exists_digon_sector
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.digon_isGFace_inner
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.isGFace_transfer_inner
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.inner_first_proper
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.inner_second_proper
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.cornerDigon_faceEdgeDoubling
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.digon_isGFace_outer
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.isGFace_transfer_outer
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.cornerDigon_outerSpur
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.exists_corner_index
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.cornerDigon_of_nonMonogon
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CornerRefine.cornerDigon_of_monogonCorner
