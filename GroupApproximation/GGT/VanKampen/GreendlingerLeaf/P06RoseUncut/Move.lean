import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.RoseCut
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06, uncut rose: the general in-place sub-walk move of a cell pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining two cells.

## The mathematics

Let `K` be a cell pocket face set of `X` between `i ≠ j`, with boundary cycle `c`.  Both proved
same-diagram steps of Piece 06 have one shape: the closed cut (`Piece06.exists_step_of_cellCut`,
new cycle `A ++ C` for `c = A ++ (B ++ C)`) and the filter move
(`Piece06.exists_step_of_cellFilterMove`, new cycle `c.filter p`).  In both, the new pocket has a
boundary cycle `L` that is part of a splitting `c ~ L ++ L'` of the old one.

`p06RoseUncut_Move K` is that shape with nothing else fixed.  It asks for

* a face set `F` off the exterior face with a relator cell `kept` in it,
* a splitting `c ~ L ++ L'` in which `L` lists exactly the boundary darts of `F`,
* `L = s₁ ++ t̄₁ ++ s₂ ++ t̄₂`, where `t̄₁`, `t̄₂` are positive proper arcs of any two distinct
  cells `i' ≠ j'` (not necessarily `i`, `j`) and `|s₁|, |s₂| ≤ ε`,
* `L` a closed dart walk,
* a dart of `L` sharing its vertex with a dart of `L'`.

**The step** (`p06RoseUncut_exists_step_of_move`).  `L` has no duplicates, being part of a
splitting of the duplicate-free cycle `c`.  So `⟨L, _, _, _⟩` is a boundary cycle of `F`, and
`CellPocketFaceSet.ofBoundaryCycle` builds a cell pocket `K'` of `X` between `i'` and `j'`.  With
letter labels the side norms are at most the side lengths
(`PocketFaceSet.wordNorm_dartWord_le_length`).  `K'` is in walk order because `L` is a closed dart
walk.  The shared vertex gives `K'.repeatedVisits < K.repeatedVisits`
(`P10Rose.length_sub_card_lt`, in `p06RoseUncut_exists_pocket_of_subwalk`).  The O-equivalence
is the identity.

The closed cut and the filter move are both instances: `P06RoseUncut/Embed.lean` and
`P06RoseUncut/Filter.lean`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated

section Move

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **An in-place sub-walk move of a cell pocket.**  The data: a face set off the exterior face
holding a relator cell, and a splitting `c ~ L ++ L'` of the boundary cycle in which `L` is the
boundary cycle of the face set.  `L` reads `s₁ t̄₁ s₂ t̄₂`, with positive proper arcs of two
distinct cells and short sides, and is a closed dart walk.  Some dart of `L` shares its vertex with
a dart of `L'`. -/
def p06RoseUncut_Move (K : CellPocketFaceSet D eps X i j) : Prop :=
  ∃ (faces : Finset X.toCombMap.Face) (kept i' j' : Fin X.rCellCount)
    (a₁ : CyclicArc (cellDarts X i')) (a₂ : CyclicArc (cellDarts X j'))
    (s₁ s₂ L L' : List X.toCombMap.Dart),
    i' ≠ j' ∧ X.outerFace ∉ faces ∧ (cell X kept).face ∈ faces ∧
      List.Perm K.boundary.cycle (L ++ L') ∧
      (∀ d, d ∈ L ↔ Surgery.MapCollapse.IsBoundaryDart X.toCombMap faces d) ∧
      L = s₁ ++ invDarts X a₁.darts ++ s₂ ++ invDarts X a₂.darts ∧
      0 < a₁.length ∧ 0 < a₂.length ∧
      a₁.length < (cellDarts X i').length ∧ a₂.length < (cellDarts X j').length ∧
      s₁.length ≤ eps ∧ s₂.length ≤ eps ∧
      IsClosedDartWalk X.toCombMap L ∧
      ∃ x ∈ L, ∃ y ∈ L', X.toCombMap.vertexOf x = X.toCombMap.vertexOf y

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseUncut_Move

/-- **The cell pocket of a sub-walk**: the face set and cycle of a sub-walk as in
`p06RoseUncut_Move` give a cell pocket of the same diagram with the given arcs, in walk order,
with strictly fewer repeated visits. -/
theorem p06RoseUncut_exists_pocket_of_subwalk (K : CellPocketFaceSet D eps X i j)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    {faces : Finset X.toCombMap.Face} {kept i' j' : Fin X.rCellCount}
    {a₁ : CyclicArc (cellDarts X i')} {a₂ : CyclicArc (cellDarts X j')}
    {s₁ s₂ L L' : List X.toCombMap.Dart} (hout : X.outerFace ∉ faces)
    (hkept : (cell X kept).face ∈ faces) (hperm : List.Perm K.boundary.cycle (L ++ L'))
    (hmem : ∀ d, d ∈ L ↔ Surgery.MapCollapse.IsBoundaryDart X.toCombMap faces d)
    (hdec : L = s₁ ++ invDarts X a₁.darts ++ s₂ ++ invDarts X a₂.darts)
    (hpos₁ : 0 < a₁.length) (hpos₂ : 0 < a₂.length) (hs₁ : s₁.length ≤ eps)
    (hs₂ : s₂.length ≤ eps) (hwalk : IsClosedDartWalk X.toCombMap L) {x y : X.toCombMap.Dart}
    (hx : x ∈ L) (hy : y ∈ L') (hxy : X.toCombMap.vertexOf x = X.toCombMap.vertexOf y) :
    ∃ K' : CellPocketFaceSet D eps X i' j', K'.ClosedWalk ∧ K'.firstArc = a₁ ∧
      K'.secondArc = a₂ ∧ K'.repeatedVisits < K.repeatedVisits := by
  have hnd : L.Nodup := (List.nodup_append.mp (K.boundary.cycle_nodup.perm hperm)).1
  obtain ⟨hne, hch, hcl⟩ := hwalk
  refine ⟨CellPocketFaceSet.ofBoundaryCycle (faces := faces) ⟨L, hne, hnd, hmem⟩
      kept a₁ a₂ s₁ s₂ hdec hout hpos₁ hpos₂ hkept hs₁ hs₂
      ((PocketFaceSet.wordNorm_dartWord_le_length hlabel s₁).trans hs₁)
      ((PocketFaceSet.wordNorm_dartWord_le_length hlabel s₂).trans hs₂), ?_, rfl, rfl, ?_⟩
  · exact ⟨hch, hcl⟩
  · unfold CellPocketFaceSet.repeatedVisits
    exact P10Rose.length_sub_card_lt X.toCombMap.vertexOf hperm hx hy hxy

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseUncut_exists_pocket_of_subwalk

/-- **The rose step from an in-place sub-walk move**, in the form of `CellRoseStepStatement`: the
same diagram, the identity O-equivalence, the cells of the move. -/
theorem p06RoseUncut_exists_step_of_move
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hmove : p06RoseUncut_Move K) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
        K'.secondArc.length < (cellDarts X' j').length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  obtain ⟨faces, kept, i', j', a₁, a₂, s₁, s₂, L, L', hij', hout, hkept, hperm, hmem, hdec,
    hpos₁, hpos₂, hlt₁, hlt₂, hs₁, hs₂, hwalk, x, hx, y, hy, hxy⟩ := hmove
  obtain ⟨K', hK', h₁, h₂, hlt⟩ := p06RoseUncut_exists_pocket_of_subwalk K hlabel hout hkept
    hperm hmem hdec hpos₁ hpos₂ hs₁ hs₂ hwalk hx hy hxy
  refine ⟨X, i', j', K', ⟨OEquivalentDiscDiagram.refl X⟩, hlabel, hij', hK', ?_, ?_, hlt⟩
  · rw [h₁]
    exact hlt₁
  · rw [h₂]
    exact hlt₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.p06RoseUncut_exists_step_of_move

end Move

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06
