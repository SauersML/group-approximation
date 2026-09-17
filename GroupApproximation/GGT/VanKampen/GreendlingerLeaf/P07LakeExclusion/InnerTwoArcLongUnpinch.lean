import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArcLongDoubling
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.LakesSurgery
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellGoodCorners
import GroupApproximation.GGT.VanKampen.Estimating.OsinEnclosedLoopPocketUnpinch
import GroupApproximation.Meta.AxiomGuard

/-!
# A two-arc lake exit from an enclosed face set

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), lane `P07InnerTwoArcLong`.  Take an
enclosed face set of `X`, turning to its successors and holding a relator cell.  Suppose its
inverse outside walk reads `s_1 Ā_1 s_2 Ā_2`, where `A_1`, `A_2` are arcs of cells outside and
`|s_1|, |s_2| ≤ ε`.  If relator words are longer than one letter, this gives
`Piece06.LakeFillTwoArcExit D ε X` (`lakeFillTwoArcExit_of_enclosed`).  Nothing about pinches is
assumed, because the unpinch is proved here.

## Proof route

* **Both arcs nonempty** (`twoArcExit_of_pos`).  Double the bridges (`twoArcOutput`, in
  `InnerTwoArcLongDoubling`).  This gives an O-equivalent copy with a bridge-free walk, the same
  side words, and so the same side lengths.  A bridge-free enclosed walk is a boundary cycle
  (`EnclosedLoopPocket.enclosedBoundaryCycle`), so `CellPocketFaceSet.ofBoundaryCycle` builds a
  cell pocket.  It is in first-turn order, which is `EnclosedLoopPocket.pocketFaceSet_firstTurns`
  on the same boundary cycle.  `copyRegion_of_firstTurns` then unpinches it into the exit
  (`twoArcExit_of_free`).
* **`A_1` empty** (`twoArcExit_of_empty`).  The walk reads `(s_1 s_2) Ā_2`.  The closed one-arc
  pieces (`enclosedLoopPocketRegionSucc_of_pieces`) give a pocket region reading `s' Ā'` with the
  word of `s'` equal to `s_1 s_2`.  Split `s'` at `|s_1|` around the empty arc
  (`split_decomposition`).

The caller supplies `A_1` empty or `A_2` nonempty.  A walk reading `s_1 Ā_1 s_2` rotates to
`s_2 ∅ s_1 Ā_1`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- Equal dart words have equal lengths. -/
theorem length_eq_of_dartWord_eq {X X' : DiscDiagram.{u, w, v} W} {s : List X.toCombMap.Dart}
    {s' : List X'.toCombMap.Dart} (h : dartWord X' s' = dartWord X s) : s'.length = s.length := by
  have h' := congrArg List.length h
  simp only [dartWord, List.length_map] at h'
  exact h'

/-- A two-arc lake exit of an O-equivalent copy is a two-arc lake exit. -/
theorem lakeFillTwoArcExit_of_oEquivalent {D : RelGenSet G Lambda} {eps : ℕ}
    {X X₁ : DiscDiagram.{u, w, v} W} (e : OEquivalentDiscDiagram X X₁)
    (h : Piece06.LakeFillTwoArcExit D eps X₁) : Piece06.LakeFillTwoArcExit D eps X := by
  obtain ⟨X', P, C, i', j', A₁, A₂, s₁, s₂, ⟨e'⟩, hlabel, hin, hout, hC, hCf, hi, hj, hdec, hn₁,
    hn₂⟩ := h
  exact ⟨X', P, C, i', j', A₁, A₂, s₁, s₂, ⟨e.trans e'⟩, hlabel, hin, hout, hC, hCf, hi, hj, hdec,
    hn₁, hn₂⟩

/-- **The exit from a bridge-free enclosed walk with two nonempty arcs.**  The walk is a boundary
cycle, the cell pocket on it is in first-turn order, and `copyRegion_of_firstTurns` unpinches it. -/
theorem twoArcExit_of_free {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}
    (hW : ∀ word ∈ W, 1 < word.length)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    {faces : Finset X.toCombMap.Face} {outerWalk : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X faces outerWalk)
    (hfree : ∀ d ∈ outerWalk, X.toCombMap.alpha d ∉ outerWalk)
    {C : RelatorCell X.toCombMap X.outerFace W} (hC : C ∈ X.relatorCells) (hCf : C.face ∈ faces)
    {k₁ k₂ : Fin X.rCellCount} (hk₂ : (cell X k₂).face ∉ faces)
    (A₁ : CyclicArc (cellDarts X k₁)) (A₂ : CyclicArc (cellDarts X k₂))
    {s₁ s₂ : List X.toCombMap.Dart}
    (hdec : invDarts X outerWalk = s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts)
    (hpos₁ : 0 < A₁.length) (hpos₂ : 0 < A₂.length)
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps) : Piece06.LakeFillTwoArcExit D eps X := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hC
  have hK := EnclosedLoopPocket.pocketFaceSet_firstTurns D E hfree ⟨k, hk⟩ hCf k₂ hk₂ A₂
    (s₁ ++ invDarts X A₁.darts ++ s₂) hdec
  obtain ⟨X', hE, hlabel', P, C', i', j', s₁', s₂', A₁', A₂', hC', hCf', hi', hj', hdec', hn₁,
      hn₂, hin, hout⟩ :=
    (CellPocketFaceSet.ofBoundaryCycle (D := D) (eps := eps)
      (EnclosedLoopPocket.enclosedBoundaryCycle E hfree) ⟨k, hk⟩ A₁ A₂ s₁ s₂
      (by
        show outerWalk.reverse.map X.toCombMap.alpha =
          s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts
        exact hdec)
      E.outerFace_not_mem hpos₁ hpos₂ hCf hs₁ hs₂
      ((PocketFaceSet.wordNorm_dartWord_le_length hlabel s₁).trans hs₁)
      ((PocketFaceSet.wordNorm_dartWord_le_length hlabel s₂).trans hs₂)).copyRegion_of_firstTurns
      hW hlabel hK
  exact ⟨X', P, C', i', j', A₁', A₂', s₁', s₂', hE, hlabel', hin, hout, hC', hCf', hi', hj', hdec',
    hn₁, hn₂⟩

/-- **The exit from an enclosed walk with two nonempty arcs**: double the bridges, then
`twoArcExit_of_free`. -/
theorem twoArcExit_of_pos {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}
    (hW : ∀ word ∈ W, 1 < word.length)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    {faces : Finset X.toCombMap.Face} {outerWalk : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X faces outerWalk)
    {C : RelatorCell X.toCombMap X.outerFace W} (hC : C ∈ X.relatorCells) (hCf : C.face ∈ faces)
    {k₁ k₂ : Fin X.rCellCount} (hk₁ : (cell X k₁).face ∉ faces) (hk₂ : (cell X k₂).face ∉ faces)
    (A₁ : CyclicArc (cellDarts X k₁)) (A₂ : CyclicArc (cellDarts X k₂))
    {s₁ s₂ : List X.toCombMap.Dart}
    (hdec : invDarts X outerWalk = s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts)
    (hpos₁ : 0 < A₁.length) (hpos₂ : 0 < A₂.length)
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps) : Piece06.LakeFillTwoArcExit D eps X := by
  obtain ⟨X₁, faces₁, walk₁, C₁, i₁, j₁, B₁, B₂, t₁, t₂, ⟨e₁⟩, hlabel₁, E₁, hfree₁, hC₁, hCf₁,
      -, hj₁, hdec₁, hpos₁₁, hpos₂₁, hword₁, hword₂⟩ :=
    EnclosedBridgeDoubling.twoArcOutput _ X faces outerWalk rfl hlabel E C hC hCf k₁ hk₁ k₂ hk₂
      A₁ A₂ s₁ s₂ hdec hpos₁ hpos₂
  exact lakeFillTwoArcExit_of_oEquivalent e₁
    (twoArcExit_of_free hW hlabel₁ E₁ hfree₁ hC₁ hCf₁ hj₁ B₁ B₂ hdec₁ hpos₁₁ hpos₂₁
      ((length_eq_of_dartWord_eq hword₁).trans_le hs₁)
      ((length_eq_of_dartWord_eq hword₂).trans_le hs₂))

/-- **The exit from an enclosed walk whose first arc is empty**: the closed one-arc pieces on the
side `s_1 s_2`, split at `|s_1|` around the empty arc. -/
theorem twoArcExit_of_empty {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W}
    (hW : ∀ word ∈ W, 1 < word.length)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    {faces : Finset X.toCombMap.Face} {outerWalk : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X faces outerWalk)
    {C : RelatorCell X.toCombMap X.outerFace W} (hC : C ∈ X.relatorCells) (hCf : C.face ∈ faces)
    {k₁ k₂ : Fin X.rCellCount} (hk₂ : (cell X k₂).face ∉ faces)
    (A₁ : CyclicArc (cellDarts X k₁)) (A₂ : CyclicArc (cellDarts X k₂))
    {s₁ s₂ : List X.toCombMap.Dart}
    (hdec : invDarts X outerWalk = s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts)
    (h0 : A₁.length = 0)
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps) : Piece06.LakeFillTwoArcExit D eps X := by
  have hA : A₁.darts = [] := by
    simp only [CyclicArc.darts, h0, List.take_zero]
  have hdec₁ : invDarts X outerWalk = (s₁ ++ s₂) ++ invDarts X A₂.darts := by
    rw [hdec, hA]
    simp only [invDarts, List.reverse_nil, List.map_nil, List.append_nil]
  obtain ⟨X', P, C', i', A', s', ⟨e⟩, hlabel', hin, hout, hC', hCf', hi', hdec', hword⟩ :=
    enclosedLoopPocketRegionSucc_of_pieces.{u, w, v} enclosedBridgeDoublingSideArcSucc.{u, w, v}
      enclosedLoopPocketUnpinchSucc.{u, w, v} D hW X hlabel faces outerWalk E C hC hCf k₂ hk₂ A₂
      (s₁ ++ s₂) hdec₁
  exact ⟨X', P, C', i', i', emptyArc (cellDarts X' i'), A', s'.take s₁.length,
    s'.drop s₁.length, ⟨e⟩, hlabel', hin, hout, hC', hCf', hi', hi',
    split_decomposition i' s₁.length hdec', wordNorm_take_le hlabel hword hs₁,
    wordNorm_drop_le hlabel hword hs₂⟩

/-- **The two-arc lake exit from an enclosed face set.**  If relator words are longer than one
letter, an enclosed face set turning to its successors does the following: it holds a relator
cell, and its inverse outside walk reads `s_1 Ā_1 s_2 Ā_2` with arcs of cells outside,
`|s_1|, |s_2| ≤ ε`, and `A_1` empty or `A_2` nonempty.  Such a face set gives the two-arc lake
exit. -/
theorem lakeFillTwoArcExit_of_enclosed {D : RelGenSet G Lambda} {eps : ℕ}
    {X : DiscDiagram.{u, w, v} W} (hW : ∀ word ∈ W, 1 < word.length)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    {faces : Finset X.toCombMap.Face} {outerWalk : List X.toCombMap.Dart}
    (E : EnclosedFaceSetSucc X faces outerWalk)
    {C : RelatorCell X.toCombMap X.outerFace W} (hC : C ∈ X.relatorCells) (hCf : C.face ∈ faces)
    {k₁ k₂ : Fin X.rCellCount} (hk₁ : (cell X k₁).face ∉ faces) (hk₂ : (cell X k₂).face ∉ faces)
    (A₁ : CyclicArc (cellDarts X k₁)) (A₂ : CyclicArc (cellDarts X k₂))
    {s₁ s₂ : List X.toCombMap.Dart}
    (hdec : invDarts X outerWalk = s₁ ++ invDarts X A₁.darts ++ s₂ ++ invDarts X A₂.darts)
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps) (hpos : A₁.length = 0 ∨ 0 < A₂.length) :
    Piece06.LakeFillTwoArcExit D eps X := by
  by_cases h0 : A₁.length = 0
  · exact twoArcExit_of_empty hW hlabel E hC hCf hk₂ A₁ A₂ hdec h0 hs₁ hs₂
  · exact twoArcExit_of_pos hW hlabel E hC hCf hk₁ hk₂ A₁ A₂ hdec (Nat.pos_of_ne_zero h0)
      (hpos.resolve_left h0) hs₁ hs₂

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.length_eq_of_dartWord_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.lakeFillTwoArcExit_of_oEquivalent
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.twoArcExit_of_free
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.twoArcExit_of_pos
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.twoArcExit_of_empty
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.lakeFillTwoArcExit_of_enclosed
