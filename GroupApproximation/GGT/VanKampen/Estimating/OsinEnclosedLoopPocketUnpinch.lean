import GroupApproximation.GGT.VanKampen.Estimating.OsinEnclosedSubdiagramLoopCutSuccProof
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGoodCornersSection
import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedPocketRegion
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionSimpleWalk
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSideFaces
import GroupApproximation.Meta.AxiomGuard

/-!
# Unpinching a bridge-free enclosed walk that reads a side and an arc

`EnclosedLoopPocketUnpinchSuccStatement` (`OsinEnclosedSubdiagramLoopCutSuccProof`): over relator
words longer than one letter, a bridge-free outside walk turning to its successor, whose inverse
reads a side `s` and then an arc `A` of a cell outside, has an O-equivalent copy with a pocket region
whose two cycles follow their boundaries.  The pocket region reads a side with the word of `s` and
then an arc of a cell outside.

The walk is a section pocket (`PocketFaceSet`) with `s` as its first side, `A` as its source arc,
an empty second side, and an empty target arc between the positions `0` and `0`.  The side bounds
are `ε' = max ‖s‖ |s|`.  The landed pinch in first-turn order
(`PocketFaceSet.exists_simple_of_firstTurns`) forgets the sides of the simple copy.  Its steps keep
them, so the two inductions are run again here with that invariant (`PocketFaceSet.ReadsSide`):
* doubling inside at a bad corner maps the sides through the embedding, which keeps labels;
* the split at a turn keeps the sides and the labels.

* `PocketFaceSet.ReadsSide`, `readsSide_faceEdgeDoublingInside`, `readsSide_pinchSplitInside`.
* `PocketFaceSet.exists_goodCorners_readsSide`, `PocketFaceSet.exists_simple_of_firstTurns_readsSide`.
* `EnclosedLoopPocket.enclosedNoncrossing`, `EnclosedLoopPocket.enclosedSideFaces_eq`,
  `EnclosedLoopPocket.enclosedBoundaryCycle`: the inverse walk as a boundary cycle of the faces.
* `EnclosedLoopPocket.pocketFaceSet`, `EnclosedLoopPocket.pocketFaceSet_firstTurns`.
* `enclosedLoopPocketUnpinchSucc : EnclosedLoopPocketUnpinchSuccStatement`.
* `enclosedSubdiagramLoopCutSuccLong_of_doubling`: the restricted successor-form loop cut from the
  side-and-arc doubling.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemmas 9.4 and 9.7); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides WordMetric

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lo hi : ℕ}

/-- **A pocket reading one side**: the second side is empty and the first side reads `sw`. -/
def ReadsSide {X : DiscDiagram.{u, w, v} W} (K : PocketFaceSet D eps X lo hi)
    (sw : List (RelLetter G Lambda)) : Prop :=
  K.secondSide = [] ∧ dartWord X K.firstSide = sw

/-- The doubling inside the face set keeps the sides and their words. -/
theorem readsSide_faceEdgeDoublingInside {X : DiscDiagram.{u, w, v} W}
    {K : PocketFaceSet D eps X lo hi} {sw : List (RelLetter G Lambda)} (hK : K.ReadsSide sw)
    (f : X.toCombMap.Face) (j : Fin (X.faceBoundary f).darts.length)
    (hlen : 1 < (X.faceBoundary f).darts.length) (hf : f ≠ X.outerFace) (hs : f ∈ K.faces) :
    (K.faceEdgeDoublingInside f j hlen hf hs).ReadsSide sw := by
  refine ⟨?_, ?_⟩
  · show K.secondSide.map (FaceEdgeDoubling.embedding X f j hlen hf).darts = []
    rw [hK.1, List.map_nil]
  · show dartWord (FaceEdgeDoubling.diagram X f j hlen hf)
      (K.firstSide.map (FaceEdgeDoubling.embedding X f j hlen hf).darts) = sw
    rw [← hK.2]
    unfold dartWord
    rw [List.map_map]
    exact List.map_congr_left fun d _ => (FaceEdgeDoubling.embedding X f j hlen hf).label d

/-- The split at a turn keeps the sides and the labels. -/
theorem readsSide_pinchSplitInside {X : DiscDiagram.{u, w, v} W} [DecidableEq X.toCombMap.Dart]
    {K : PocketFaceSet D eps X lo hi} {sw : List (RelLetter G Lambda)} (hK : K.ReadsSide sw)
    (I : PinchSplit.Input X) (hs : I.Inside K.faces) :
    (K.pinchSplitInside I hs).ReadsSide sw :=
  hK

/-- **Good corners, keeping the side.**  `exists_goodCorners`, with the invariant carried through
the doublings. -/
theorem exists_goodCorners_readsSide {X : DiscDiagram.{u, w, v} W}
    (K : PocketFaceSet D eps X lo hi) (hW : ∀ word ∈ W, 1 < word.length)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) (hK : K.FirstTurns)
    {sw : List (RelLetter G Lambda)} (hread : K.ReadsSide sw) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
        K'.FirstTurns ∧ K'.GoodCorners ∧ K'.repeatedVisits = K.repeatedVisits ∧
        K'.ReadsSide sw := by
  have H : ∀ (n : ℕ) (X : DiscDiagram.{u, w, v} W) (K : PocketFaceSet D eps X lo hi),
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) → K.FirstTurns → K.ReadsSide sw →
        K.badCorners = n →
        ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
            K'.FirstTurns ∧ K'.GoodCorners ∧ K'.repeatedVisits = K.repeatedVisits ∧
            K'.ReadsSide sw := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih X K hlabel hK hread hn
    by_cases hgood : K.GoodCorners
    · exact ⟨X, K, ⟨OEquivalentDiscDiagram.refl X⟩, hlabel, hK, hgood, rfl, hread⟩
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
      obtain ⟨X₂, K₂, ⟨e₂⟩, hlabel₂, hK₂, hgood₂, hvis₂, hread₂⟩ :=
        ih _ (lt_of_lt_of_eq hlt hn) _
          (K.faceEdgeDoublingInside (X.toCombMap.faceOf d) k hlen hf hs)
          (FaceEdgeDoubling.label_letter X (X.toCombMap.faceOf d) k hlen hf hlabel)
          (K.faceEdgeDoublingInside_firstTurns (X.toCombMap.faceOf d) k hlen hf hs hK)
          (readsSide_faceEdgeDoublingInside hread (X.toCombMap.faceOf d) k hlen hf hs) rfl
      exact ⟨X₂, K₂,
        ⟨(FaceEdgeDoubling.oEquivalent X (X.toCombMap.faceOf d) k hlen hf).trans e₂⟩, hlabel₂,
        hK₂, hgood₂,
        hvis₂.trans (K.faceEdgeDoublingInside_repeatedVisits (X.toCombMap.faceOf d) k hlen hf hs),
        hread₂⟩
  exact H _ X K hlabel hK hread rfl

/-- **The pinch in first-turn order, keeping the side.**  `exists_simple_of_firstTurns`, with the
invariant carried through the doublings and the splits. -/
theorem exists_simple_of_firstTurns_readsSide {X : DiscDiagram.{u, w, v} W}
    (K : PocketFaceSet D eps X lo hi) (hW : ∀ word ∈ W, 1 < word.length)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) (hK : K.FirstTurns)
    {sw : List (RelLetter G Lambda)} (hread : K.ReadsSide sw) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ K'.Simple ∧ K'.ReadsSide sw := by
  have H : ∀ (n : ℕ) (X : DiscDiagram.{u, w, v} W) (K : PocketFaceSet D eps X lo hi),
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) → K.FirstTurns → K.ReadsSide sw →
        K.repeatedVisits = n →
        ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ K'.Simple ∧
            K'.ReadsSide sw := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih X K hlabel hK hread hn
    obtain ⟨X₁, K₁, ⟨e₁⟩, hlabel₁, hK₁, hgood₁, hvis₁, hread₁⟩ :=
      K.exists_goodCorners_readsSide hW hlabel hK hread
    by_cases hpinch : Unpinched X₁.toCombMap K₁.faces
    · exact ⟨X₁, K₁, ⟨e₁⟩, hlabel₁, K₁.simple_of_closedWalk_of_unpinched hK₁.closedWalk hpinch,
        hread₁⟩
    · classical
      obtain ⟨d₀, hd₀, e₀, he₀, e, he, hne₀, hne, hv, hturn⟩ :=
        K₁.exists_turn_of_not_unpinched hK₁ hpinch
      obtain ⟨k₀, -, hk₀, hkeep₀⟩ := FirstTurn.reverse_map_alpha_iff.mp hturn
      obtain ⟨I, hx, hy, hs⟩ := K₁.exists_turnInput hd₀ he₀ hk₀
        (fun h => hne₀ (hgood₁.2 d₀ hd₀ e₀ he₀ h)) (hgood₁.1 d₀ hd₀) (hgood₁.1 e₀ he₀)
      have hlt :=
        K₁.pinchSplitInside_repeatedVisits_lt_of_turn I hs hd₀ he₀ hx hy hk₀ hkeep₀ he hne hv
      obtain ⟨X₃, K₃, ⟨e₃⟩, hlabel₃, hsimple₃, hread₃⟩ :=
        ih _ (lt_of_lt_of_eq (lt_of_lt_of_eq hlt hvis₁) hn) I.diagram (K₁.pinchSplitInside I hs)
          (I.label_isLetter (symmetricLabelAlphabet D) hlabel₁)
          (K₁.firstTurns_pinchSplitInside I hs hd₀ he₀ hx hy hK₁)
          (readsSide_pinchSplitInside hread₁ I hs) rfl
      exact ⟨X₃, K₃, ⟨(e₁.trans I.oEquivalent).trans e₃⟩, hlabel₃, hsimple₃, hread₃⟩
  exact H _ X K hlabel hK hread rfl

end PocketFaceSet

namespace EnclosedLoopPocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W} {faces : Finset X.toCombMap.Face}
  {outerWalk : List X.toCombMap.Dart}

/-- The inverse walk of a bridge-free enclosed walk turning to its successor is noncrossing. -/
theorem enclosedNoncrossing (E : EnclosedFaceSetSucc X faces outerWalk)
    (hfree : ∀ d ∈ outerWalk, X.toCombMap.alpha d ∉ outerWalk) :
    IsNoncrossingClosedWalk X.toCombMap (outerWalk.reverse.map X.toCombMap.alpha) :=
  FirstTurnWalk.isNoncrossingClosedWalk_reverse X.planar E.ne_nil E.nodup hfree
    (EnclosedPocketRegion.isChain_firstTurn E) (EnclosedPocketRegion.firstTurn_close E)

/-- The faces on the side of the inverse walk are the enclosed faces. -/
theorem enclosedSideFaces_eq (E : EnclosedFaceSetSucc X faces outerWalk)
    (hfree : ∀ d ∈ outerWalk, X.toCombMap.alpha d ∉ outerWalk) :
    sideFaces X.toCombMap (outerWalk.reverse.map X.toCombMap.alpha) = faces :=
  Finset.Subset.antisymm (EnclosedPocketRegion.sideFaces_subset E.toEnclosedFaceSet hfree)
    (EnclosedPocketRegion.subset_sideFaces E.toEnclosedFaceSet)

/-- **The inverse walk as a boundary cycle of the enclosed faces.** -/
noncomputable def enclosedBoundaryCycle (E : EnclosedFaceSetSucc X faces outerWalk)
    (hfree : ∀ d ∈ outerWalk, X.toCombMap.alpha d ∉ outerWalk) :
    Surgery.MapCollapse.BoundaryCycle X.toCombMap faces where
  cycle := outerWalk.reverse.map X.toCombMap.alpha
  cycle_nonempty := (enclosedNoncrossing E hfree).ne_nil
  cycle_nodup := (enclosedNoncrossing E hfree).nodup
  cycle_mem_iff d := by
    rw [← enclosedSideFaces_eq E hfree]
    exact ((enclosedNoncrossing E hfree).isBoundaryDart_sideFaces_iff X.planar d).symm

/-- **The one-sided section pocket of the walk.**  First side `s`, source arc `A`, an empty second
side and an empty target arc between the positions `0` and `0`, with side bounds `max ‖s‖ |s|`. -/
noncomputable def pocketFaceSet (D : RelGenSet G Lambda) (E : EnclosedFaceSetSucc X faces outerWalk)
    (hfree : ∀ d ∈ outerWalk, X.toCombMap.alpha d ∉ outerWalk)
    (kept : Fin X.rCellCount) (hkept : (cell X kept).face ∈ faces)
    (i : Fin X.rCellCount) (hi : (cell X i).face ∉ faces)
    (A : CyclicArc (cellDarts X i)) (s : List X.toCombMap.Dart)
    (hdec : invDarts X outerWalk = s ++ invDarts X A.darts) :
    PocketFaceSet D (max (wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X s))) s.length)
      X 0 0 where
  faces := faces
  outerFace_not_mem := E.outerFace_not_mem
  source := i
  source_not_mem := hi
  kept := kept
  kept_mem := hkept
  sourceArc := A
  targetArc := ⟨⟨0, Nat.succ_pos _⟩, 0, Nat.zero_le _⟩
  firstSide := s
  secondSide := []
  boundary := enclosedBoundaryCycle E hfree
  decomposition := by
    show outerWalk.reverse.map X.toCombMap.alpha = s ++ invDarts X A.darts ++ [] ++ []
    rw [List.append_nil, List.append_nil]
    exact hdec
  firstSide_length_le := le_max_right _ _
  secondSide_length_le := Nat.zero_le _
  firstSide_norm_le := le_max_left _ _
  secondSide_norm_le := by
    show wordNorm D.alphabet.carrier (RelLetter.listVal ([] : List (RelLetter G Lambda))) ≤ _
    rw [RelLetter.listVal_nil, WordMetric.wordNorm_one]
    exact Nat.zero_le _
  lo_le := Nat.zero_le _
  le_hi := Nat.le_refl 0

/-- The one-sided section pocket is in first-turn order. -/
theorem pocketFaceSet_firstTurns (D : RelGenSet G Lambda)
    (E : EnclosedFaceSetSucc X faces outerWalk)
    (hfree : ∀ d ∈ outerWalk, X.toCombMap.alpha d ∉ outerWalk)
    (kept : Fin X.rCellCount) (hkept : (cell X kept).face ∈ faces)
    (i : Fin X.rCellCount) (hi : (cell X i).face ∉ faces)
    (A : CyclicArc (cellDarts X i)) (s : List X.toCombMap.Dart)
    (hdec : invDarts X outerWalk = s ++ invDarts X A.darts) :
    (pocketFaceSet D E hfree kept hkept i hi A s hdec).FirstTurns := by
  have key : ∀ (c : List X.toCombMap.Dart), c = outerWalk → ∀ hne : c ≠ [],
      c.IsChain (FirstTurn X.toCombMap c) ∧
        FirstTurn X.toCombMap c (c.getLast hne) (c.head hne) := by
    intro c hc hne
    subst hc
    exact ⟨EnclosedPocketRegion.isChain_firstTurn E, EnclosedPocketRegion.firstTurn_close E⟩
  have hc : (outerWalk.reverse.map X.toCombMap.alpha).reverse.map X.toCombMap.alpha = outerWalk :=
    FirstTurnWalk.reverse_map_alpha_involutive outerWalk
  have hne : (outerWalk.reverse.map X.toCombMap.alpha).reverse.map X.toCombMap.alpha ≠ [] := by
    rw [hc]
    exact E.ne_nil
  exact (PocketFaceSet.firstTurns_iff _ hne).mpr (key _ hc hne)

end EnclosedLoopPocket

/-- **`EnclosedLoopPocketUnpinchSuccStatement` holds.** -/
theorem enclosedLoopPocketUnpinchSucc : EnclosedLoopPocketUnpinchSuccStatement.{u, w, v} := by
  intro G _ Lambda W D hW X hlabel faces outerWalk E hfree C hC hCf i hi A s hdec
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hC
  obtain ⟨X', K', ⟨e⟩, hlabel', hsimple, hread⟩ :=
    (EnclosedLoopPocket.pocketFaceSet D E hfree ⟨k, hk⟩ hCf i hi A s hdec).exists_simple_of_firstTurns_readsSide
      hW hlabel (EnclosedLoopPocket.pocketFaceSet_firstTurns D E hfree ⟨k, hk⟩ hCf i hi A s hdec)
      (sw := dartWord X s) ⟨rfl, rfl⟩
  have hfaces : sideFaces X'.toCombMap K'.boundary.cycle = K'.faces :=
    sideFaces_boundaryCycle_eq (CombMap.connected_of_planar _ X'.planar) K'.boundary
      K'.outerFace_not_mem
  have hout : X'.outerFace ∉ sideFaces X'.toCombMap K'.boundary.cycle := by
    rw [hfaces]
    exact K'.outerFace_not_mem
  have hw := hsimple.isSimpleClosedWalk
  have h0 : K'.targetArc.length = 0 := by
    have h := K'.le_hi
    omega
  have hdarts : K'.targetArc.darts = [] := by
    simp only [CyclicArc.darts, h0, List.take_zero]
  refine ⟨X', PocketRegion.ofSimpleClosedWalk hw hout, cell X' K'.kept, K'.source, K'.sourceArc,
    K'.firstSide, ⟨e⟩, hlabel', (PocketRegion.ofSimpleClosedWalk_followsBoundary hw hout).1,
    (PocketRegion.ofSimpleClosedWalk_followsBoundary hw hout).2, cell_mem X' K'.kept, ?_, ?_, ?_,
    hread.2⟩
  · rw [PocketRegion.ofSimpleClosedWalk_faces, hfaces]
    exact K'.kept_mem
  · rw [PocketRegion.ofSimpleClosedWalk_faces, hfaces]
    exact K'.source_not_mem
  · rw [PocketRegion.ofSimpleClosedWalk_invDarts_outer, K'.decomposition, hread.1, hdarts,
      List.append_nil, List.append_nil]

/-- **The restricted successor-form loop cut from the side-and-arc doubling.** -/
theorem enclosedSubdiagramLoopCutSuccLong_of_doubling
    (hdouble : EnclosedBridgeDoublingSideArcSuccStatement.{u, w, v}) :
    EnclosedSubdiagramLoopCutSuccLongStatement.{u, w, v} :=
  enclosedSubdiagramLoopCutSuccLong_of_pocketRegion
    (enclosedLoopPocketRegionSucc_of_pieces hdouble enclosedLoopPocketUnpinchSucc)

end GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen

#audit_axioms PocketFaceSet.ReadsSide
#audit_axioms PocketFaceSet.readsSide_faceEdgeDoublingInside
#audit_axioms PocketFaceSet.readsSide_pinchSplitInside
#audit_axioms PocketFaceSet.exists_goodCorners_readsSide
#audit_axioms PocketFaceSet.exists_simple_of_firstTurns_readsSide
#audit_axioms EnclosedLoopPocket.enclosedNoncrossing
#audit_axioms EnclosedLoopPocket.enclosedSideFaces_eq
#audit_axioms EnclosedLoopPocket.enclosedBoundaryCycle
#audit_axioms EnclosedLoopPocket.pocketFaceSet
#audit_axioms EnclosedLoopPocket.pocketFaceSet_firstTurns
#audit_axioms enclosedLoopPocketUnpinchSucc
#audit_axioms enclosedSubdiagramLoopCutSuccLong_of_doubling
