import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchFirstTurn
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellTransport
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketEdgeDoublingFirstTurns
import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingFaces
import GroupApproximation.Meta.AxiomGuard

/-!
# Good corners for the pocket between two cells, and the pinch in first-turn order

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the cells `Π_i` and `Π_j`.

`cellPocketPinchGoodCornerStep` (`Estimating/OsinPocketCellPinchFirstTurn.lean`) lowers the repeated
visits of a pinched cell pocket in first-turn order with good corners, and returns first-turn order.
This module restores good corners before each step, and iterates.

A boundary dart `d` has its face inside the face set.  Good corners fail at `d` exactly when that face
is a relator face or holds a second boundary dart (`CellPocketFaceSet.BadCorner`).  In both cases the
face has more than one dart, when relator words are longer than one letter.  Doubling the edge of `d`
in its face (`CellPocketFaceSet.faceEdgeDoublingInside`) moves `d` onto the new digon, a G-face holding
no other boundary dart, and changes no other boundary dart from good to bad.  So the number of bad
corners (`badCorners`) drops, while first-turn order, letter labels and repeated visits are kept.  No
corner outside the face set is touched, so trim–double is not needed here.

* `CellPocketFaceSet.faceEdgeDoublingInside_firstTurns`: the doubling keeps first-turn order.
* `badCorner_of_faceEdgeDoublingInside`, `not_badCorner_faceEdgeDoublingInside`,
  `badCorners_faceEdgeDoublingInside_lt`: the count drops.
* `CellPocketFaceSet.exists_goodCorners`: an O-equivalent copy with letter labels and good corners, in
  first-turn order, with the same repeated visits.
* `CellPocketFaceSet.exists_simple_of_firstTurns`, `CellPocketPinchFirstTurnsStatement`,
  `cellPocketPinchFirstTurns`: a cell pocket in first-turn order of a diagram with letter labels, over
  relator words longer than one letter, has an O-equivalent copy with letter labels and a simple cell
  pocket face set.
* `CellPocketFaceSet.copyRegion_of_firstTurns`: the region data of the copy form of
  `MultipleEdgePocketRegionInput`, from first-turn order alone.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded WordMetric Surgery.MapCollapse

namespace CellPocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A bad corner** of a cell pocket: the face of the dart is a relator face, or holds another
boundary dart. -/
def BadCorner (K : CellPocketFaceSet D eps X i j) (d : X.toCombMap.Dart) : Prop :=
  (∃ C ∈ X.relatorCells, C.face = X.toCombMap.faceOf d) ∨
    ∃ e ∈ K.boundary.cycle, e ≠ d ∧ X.toCombMap.faceOf e = X.toCombMap.faceOf d

open Classical in
/-- **The number of bad corners** along the boundary cycle. -/
noncomputable def badCorners (K : CellPocketFaceSet D eps X i j) : ℕ :=
  K.boundary.cycle.countP fun d => decide (K.BadCorner d)

/-- A cell pocket without good corners has a bad corner on its boundary cycle. -/
theorem exists_badCorner_of_not_goodCorners (K : CellPocketFaceSet D eps X i j)
    (h : ¬ K.GoodCorners) : ∃ d ∈ K.boundary.cycle, K.BadCorner d := by
  by_contra hno
  apply h
  unfold CellPocketFaceSet.GoodCorners
  exact ⟨fun d hd C hC hCd => hno ⟨d, hd, Or.inl ⟨C, hC, hCd⟩⟩,
    fun d hd e he hde => Classical.byContradiction fun hne =>
      hno ⟨e, he, Or.inr ⟨d, hd, hne, hde⟩⟩⟩

/-- **The face of a bad corner has more than one dart**, over relator words longer than one
letter. -/
theorem one_lt_length_of_badCorner (K : CellPocketFaceSet D eps X i j)
    (hW : ∀ word ∈ W, 1 < word.length) {d : X.toCombMap.Dart} (hbad : K.BadCorner d) :
    1 < (X.faceBoundary (X.toCombMap.faceOf d)).darts.length := by
  rcases hbad with ⟨C, hC, hCd⟩ | ⟨e, -, hne, hface⟩
  · rw [← hCd]
    exact CornerCount.one_lt_length_of_relatorCell X hW hC
  · exact CornerCount.one_lt_length_of_mem_ne
      (((X.faceBoundary (X.toCombMap.faceOf d)).mem_iff e).mpr hface)
      (((X.faceBoundary (X.toCombMap.faceOf d)).mem_iff d).mpr rfl) hne

section Doubling

variable (K : CellPocketFaceSet D eps X i j) (f : X.toCombMap.Face)
  (k : Fin (X.faceBoundary f).darts.length) (hlen : 1 < (X.faceBoundary f).darts.length)
  (hf : f ≠ X.outerFace) (hs : f ∈ K.faces)

/-- **The doubling inside the face set keeps first-turn order.** -/
theorem faceEdgeDoublingInside_firstTurns (hK : K.FirstTurns) :
    (K.faceEdgeDoublingInside f k hlen hf hs).FirstTurns :=
  EdgeInsertion.firstTurnChain_map_embed
    (EdgeInsertion.corners_ne X.toCombMap (FaceEdgeDoubling.rebased X f k)
      (FaceEdgeDoubling.second X f k hlen) Nat.one_pos)
    K.boundary.cycle_nonempty (K.faceEdgeDoublingInside f k hlen hf hs).boundary.cycle_nonempty hK

/-- **A dart bad after the doubling was bad before**, away from the doubled dart. -/
theorem badCorner_of_faceEdgeDoublingInside {d z : X.toCombMap.Dart}
    (hdart : FaceEdgeDoubling.dart X f k = d) (hnez : z ≠ d)
    (h : (K.faceEdgeDoublingInside f k hlen hf hs).BadCorner
      ((FaceEdgeDoubling.embedding X f k hlen hf).darts z)) :
    K.BadCorner z := by
  subst hdart
  rcases h with ⟨C, hC, hCz⟩ | ⟨e', he', hne', hface'⟩
  · rw [FaceEdgeDoubling.faceOf_diagram_embed_of_ne X f k hlen hf hnez] at hCz
    obtain ⟨C₀, hC₀, hC₀f⟩ := FaceEdgeDoubling.exists_relatorCell_of_mem_diagram X f k hlen hf hC
    exact Or.inl ⟨C₀, hC₀, FaceEdgeDoubling.faceImage_injective X f k hlen (hC₀f.symm.trans hCz)⟩
  · rw [faceEdgeDoublingInside_boundary_cycle K f k hlen hf hs] at he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
    have hne : e ≠ z := fun hez => hne' (by rw [hez])
    rw [FaceEdgeDoubling.faceOf_diagram_embed_of_ne X f k hlen hf hnez] at hface'
    by_cases hed : e = FaceEdgeDoubling.dart X f k
    · subst hed
      rw [FaceEdgeDoubling.faceOf_diagram_embed_dart X f k hlen hf] at hface'
      exact absurd hface'.symm (FaceEdgeDoubling.faceImage_ne_digon X f k hlen _)
    · rw [FaceEdgeDoubling.faceOf_diagram_embed_of_ne X f k hlen hf hed] at hface'
      exact Or.inr ⟨e, he, hne, FaceEdgeDoubling.faceImage_injective X f k hlen hface'⟩

/-- **The doubled dart is not a bad corner after the doubling.** -/
theorem not_badCorner_faceEdgeDoublingInside {d : X.toCombMap.Dart}
    (hdart : FaceEdgeDoubling.dart X f k = d) :
    ¬ (K.faceEdgeDoublingInside f k hlen hf hs).BadCorner
      ((FaceEdgeDoubling.embedding X f k hlen hf).darts d) := by
  subst hdart
  rintro (⟨C, hC, hCd⟩ | ⟨e', he', hne', hface'⟩)
  · rw [FaceEdgeDoubling.faceOf_diagram_embed_dart X f k hlen hf] at hCd
    obtain ⟨C₀, -, hC₀f⟩ := FaceEdgeDoubling.exists_relatorCell_of_mem_diagram X f k hlen hf hC
    exact FaceEdgeDoubling.faceImage_ne_digon X f k hlen C₀.face (hC₀f.symm.trans hCd)
  · rw [faceEdgeDoublingInside_boundary_cycle K f k hlen hf hs] at he'
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp he'
    have hed : e ≠ FaceEdgeDoubling.dart X f k := fun hed => hne' (by rw [hed])
    rw [FaceEdgeDoubling.faceOf_diagram_embed_dart X f k hlen hf,
      FaceEdgeDoubling.faceOf_diagram_embed_of_ne X f k hlen hf hed] at hface'
    exact FaceEdgeDoubling.faceImage_ne_digon X f k hlen _ hface'

/-- **Doubling at a bad corner lowers the number of bad corners.** -/
theorem badCorners_faceEdgeDoublingInside_lt {d : X.toCombMap.Dart}
    (hdart : FaceEdgeDoubling.dart X f k = d) (hd : d ∈ K.boundary.cycle)
    (hbad : K.BadCorner d) :
    (K.faceEdgeDoublingInside f k hlen hf hs).badCorners < K.badCorners := by
  classical
  unfold CellPocketFaceSet.badCorners
  rw [faceEdgeDoublingInside_boundary_cycle K f k hlen hf hs, List.countP_map]
  refine CornerCount.countP_lt_countP_of_imp (fun z _ h => ?_) ⟨d, hd, ?_, ?_⟩
  · by_cases hzd : z = d
    · rw [hzd]
      exact decide_eq_true hbad
    · exact decide_eq_true
        (K.badCorner_of_faceEdgeDoublingInside f k hlen hf hs hdart hzd (of_decide_eq_true h))
  · exact decide_eq_true hbad
  · exact decide_eq_false (K.not_badCorner_faceEdgeDoublingInside f k hlen hf hs hdart)

end Doubling

/-- **Good corners, by doubling inside the face set.**  A cell pocket in first-turn order of a
diagram with letter labels, over relator words longer than one letter, has an O-equivalent copy with
letter labels and a cell pocket face set in first-turn order with good corners and the same repeated
visits. -/
theorem exists_goodCorners (K : CellPocketFaceSet D eps X i j) (hW : ∀ word ∈ W, 1 < word.length)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) (hK : K.FirstTurns) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
        K'.FirstTurns ∧ K'.GoodCorners ∧ K'.repeatedVisits = K.repeatedVisits := by
  have H : ∀ (n : ℕ) (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount)
      (K : CellPocketFaceSet D eps X i j),
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) → K.FirstTurns →
        K.badCorners = n →
        ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
          (K' : CellPocketFaceSet D eps X' i' j'),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
            K'.FirstTurns ∧ K'.GoodCorners ∧ K'.repeatedVisits = K.repeatedVisits := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih X i j K hlabel hK hn
    by_cases hgood : K.GoodCorners
    · exact ⟨X, i, j, K, ⟨OEquivalentDiscDiagram.refl X⟩, hlabel, hK, hgood, rfl⟩
    · obtain ⟨d, hd, hbad⟩ := K.exists_badCorner_of_not_goodCorners hgood
      obtain ⟨hs, -⟩ := (K.boundary.cycle_mem_iff d).mp hd
      have hf : X.toCombMap.faceOf d ≠ X.outerFace := fun h => K.outerFace_not_mem (h ▸ hs)
      obtain ⟨k, hk⟩ :=
        List.get_of_mem (((X.faceBoundary (X.toCombMap.faceOf d)).mem_iff d).mpr rfl)
      have hdart : FaceEdgeDoubling.dart X (X.toCombMap.faceOf d) k = d :=
        (FaceEdgeDoubling.dart_eq_get X (X.toCombMap.faceOf d) k).trans hk
      have hlen := K.one_lt_length_of_badCorner hW hbad
      have hlt := K.badCorners_faceEdgeDoublingInside_lt (X.toCombMap.faceOf d) k hlen hf hs hdart
        hd hbad
      obtain ⟨X₂, i₂, j₂, K₂, ⟨e₂⟩, hlabel₂, hK₂, hgood₂, hvis₂⟩ :=
        ih _ (lt_of_lt_of_eq hlt hn) _ _ _
          (K.faceEdgeDoublingInside (X.toCombMap.faceOf d) k hlen hf hs)
          (FaceEdgeDoubling.label_letter X (X.toCombMap.faceOf d) k hlen hf hlabel)
          (K.faceEdgeDoublingInside_firstTurns (X.toCombMap.faceOf d) k hlen hf hs hK) rfl
      exact ⟨X₂, i₂, j₂, K₂,
        ⟨(FaceEdgeDoubling.oEquivalent X (X.toCombMap.faceOf d) k hlen hf).trans e₂⟩, hlabel₂,
        hK₂, hgood₂,
        hvis₂.trans (K.faceEdgeDoublingInside_repeatedVisits (X.toCombMap.faceOf d) k hlen hf hs)⟩
  exact H _ X i j K hlabel hK rfl

/-- **The pinch between two cells, in first-turn order.**  Restore good corners, take the good-corner
step, and repeat: the repeated visits drop at each step, and an unpinched cell pocket in walk order is
simple. -/
theorem exists_simple_of_firstTurns (K : CellPocketFaceSet D eps X i j)
    (hW : ∀ word ∈ W, 1 < word.length)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) (hK : K.FirstTurns) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ K'.Simple := by
  have H : ∀ (n : ℕ) (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount)
      (K : CellPocketFaceSet D eps X i j),
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) → K.FirstTurns →
        K.repeatedVisits = n →
        ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
          (K' : CellPocketFaceSet D eps X' i' j'),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ K'.Simple := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih X i j K hlabel hK hn
    obtain ⟨X₁, i₁, j₁, K₁, ⟨e₁⟩, hlabel₁, hK₁, hgood₁, hvis₁⟩ :=
      K.exists_goodCorners hW hlabel hK
    by_cases hpinch : Unpinched X₁.toCombMap K₁.faces
    · exact ⟨X₁, i₁, j₁, K₁, ⟨e₁⟩, hlabel₁,
        K₁.simple_of_closedWalk_of_unpinched hK₁.closedWalk hpinch⟩
    · obtain ⟨X₂, i₂, j₂, K₂, ⟨e₂⟩, hlabel₂, hK₂, hlt⟩ :=
        K₁.exists_firstTurnStep_of_goodCorners hlabel₁ hK₁ hgood₁ hpinch
      obtain ⟨X₃, i₃, j₃, K₃, ⟨e₃⟩, hlabel₃, hsimple₃⟩ :=
        ih K₂.repeatedVisits (lt_of_lt_of_eq (lt_of_lt_of_eq hlt hvis₁) hn) X₂ i₂ j₂ K₂
          hlabel₂ hK₂ rfl
      exact ⟨X₃, i₃, j₃, K₃, ⟨(e₁.trans e₂).trans e₃⟩, hlabel₃, hsimple₃⟩
  exact H _ X i j K hlabel hK rfl

/-- **The region data of the copy form of `MultipleEdgePocketRegionInput`, from first-turn order.** -/
theorem copyRegion_of_firstTurns (K : CellPocketFaceSet D eps X i j)
    (hW : ∀ word ∈ W, 1 < word.length)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) (hK : K.FirstTurns) :
    ∃ X' : DiscDiagram.{u, w, v} W, Nonempty (OEquivalentDiscDiagram X X') ∧
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
      ∃ (P : PocketRegion X') (C : RelatorCell X'.toCombMap X'.outerFace W)
        (i' j' : Fin X'.rCellCount) (s₁ s₂ : List X'.toCombMap.Dart)
        (A₁ : CyclicArc (cellDarts X' i')) (A₂ : CyclicArc (cellDarts X' j')),
        C ∈ X'.relatorCells ∧ C.face ∈ P.faces ∧
          (cell X' i').face ∉ P.faces ∧ (cell X' j').face ∉ P.faces ∧
          invDarts X' P.outer.cycle = s₁ ++ invDarts X' A₁.darts ++ s₂ ++ invDarts X' A₂.darts ∧
          wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X' s₁)) ≤ eps ∧
          wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X' s₂)) ≤ eps ∧
          P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary := by
  obtain ⟨X', i', j', K', hE, hlabel', hsimple⟩ := K.exists_simple_of_firstTurns hW hlabel hK
  obtain ⟨P, C, hC, hCf, hi, hj, hdec, hn₁, hn₂, hin, hout, -⟩ :=
    K'.exists_pocketRegion_of_simple hsimple
  exact ⟨X', hE, hlabel', P, C, i', j', K'.firstSide, K'.secondSide, K'.firstArc, K'.secondArc,
    hC, hCf, hi, hj, hdec, hn₁, hn₂, hin, hout⟩

end CellPocketFaceSet

/-- **The pinch between two cells for a cell pocket in first-turn order.**  Over relator words
longer than one letter, a cell pocket face set in first-turn order of a diagram whose labels are
letters has an O-equivalent copy with letter labels and a simple cell pocket face set. -/
def CellPocketPinchFirstTurnsStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))), (∀ word ∈ W, 1 < word.length) →
    ∀ (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount),
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : CellPocketFaceSet D eps X i j, K.FirstTurns →
        ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
          (K' : CellPocketFaceSet D eps X' i' j'),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ K'.Simple

theorem cellPocketPinchFirstTurns : CellPocketPinchFirstTurnsStatement.{u, w, v} := by
  intro G _ Lambda D eps W hW X i j hlabel K hK
  exact K.exists_simple_of_firstTurns hW hlabel hK

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.faceEdgeDoublingInside_firstTurns
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.badCorners_faceEdgeDoublingInside_lt
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.exists_goodCorners
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.exists_simple_of_firstTurns
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.copyRegion_of_firstTurns
#audit_closed_axioms GroupApproximation.GGT.VanKampen.cellPocketPinchFirstTurns
