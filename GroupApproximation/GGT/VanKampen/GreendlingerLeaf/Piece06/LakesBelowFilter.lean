import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.RoseBelow
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06 below the bound: in-place region-union moves of a cell pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the cells `Π_i` and `Π_j`.  This module is the
cell-pocket analogue of `P10Rose/InPlaceFilter` (`filter_cycle_eq`, `step_of_filter`).

## The mathematics

Let `K` be a cell pocket face set of `X` between `i` and `j`, with boundary cycle
`c = s₁ ++ t̄₁ ++ s₂ ++ t̄₂` (`t̄₁ = invDarts X K.firstArc.darts`, `t̄₂ = invDarts X K.secondArc.darts`).

1. **Filtering** (`filter_cycle_eq_cell`).  For a Boolean predicate `p` true on `t̄₁` and `t̄₂`,
   filtering commutes with `++` and fixes both arcs, so
   `c.filter p = s₁.filter p ++ t̄₁ ++ s₂.filter p ++ t̄₂`.
2. **A move** (`CellFilterMove K`).  A face set `F'` away from the exterior face, holding a relator
   cell, whose boundary darts are exactly the darts of `c` kept by such a `p`, with `c.filter p` a
   closed dart walk and some kept dart sharing its vertex with a removed one.  The intended
   witnesses are the region-union moves `F' = (F \ Fs) ∪ Ns` of `P10Rose/InPlaceFilter` (fill some
   lakes, drop some petals away from the kept cell).
3. **The step** (`exists_step_of_cellFilterMove`).  The list `L = c.filter p` is duplicate free
   (a sub-list of `c`, through `c ~ L ++ c.filter (¬p)`, `List.filter_append_perm`), lists exactly
   the boundary darts of `F'`, and reads `s₁' ++ t̄₁ ++ s₂' ++ t̄₂` with `|sᵢ'| ≤ |sᵢ| ≤ ε`; letter
   labels bound the side norms by the side lengths.  So `CellPocketFaceSet.ofBoundaryCycle` builds a
   cell pocket `K'` of the same diagram between the same cells, with the arcs of `K` (positive, and
   both cells are off `F'` automatically).  `L` is a closed walk, so `K'` is in walk order, and the
   kept dart `x` and the removed dart `y` start at one vertex, so `P10Rose.length_sub_card_lt`
   gives `K'.repeatedVisits < K.repeatedVisits`.
4. **The rose step** (`exists_step_of_cellFilterMove'`): the identity O-equivalence, the same cells
   and proper arcs.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated

section Filter

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Filtering the boundary cycle of a cell pocket** by a predicate true on both arcs filters the
two sides and keeps the arcs. -/
theorem filter_cycle_eq_cell (K : CellPocketFaceSet D eps X i j) (p : X.toCombMap.Dart → Bool)
    (ht₁ : ∀ d ∈ invDarts X K.firstArc.darts, p d = true)
    (ht₂ : ∀ d ∈ invDarts X K.secondArc.darts, p d = true) :
    K.boundary.cycle.filter p = K.firstSide.filter p ++ invDarts X K.firstArc.darts ++
      K.secondSide.filter p ++ invDarts X K.secondArc.darts := by
  rw [K.decomposition, List.filter_append, List.filter_append, List.filter_append,
    List.filter_eq_self.mpr ht₁, List.filter_eq_self.mpr ht₂]

/-- **An in-place region-union move of a cell pocket**: a face set away from the exterior face,
holding a relator cell, whose boundary darts are the darts of the old cycle kept by a predicate true
on both arcs; the kept darts, in the order of the old cycle, form a closed walk, and some kept dart
shares its vertex with a removed one. -/
def CellFilterMove (K : CellPocketFaceSet D eps X i j) : Prop :=
  ∃ (faces : Finset X.toCombMap.Face) (kept : Fin X.rCellCount) (p : X.toCombMap.Dart → Bool),
    X.outerFace ∉ faces ∧ (cell X kept).face ∈ faces ∧
      (∀ d, Surgery.MapCollapse.IsBoundaryDart X.toCombMap faces d ↔
        d ∈ K.boundary.cycle ∧ p d = true) ∧
      (∀ d ∈ invDarts X K.firstArc.darts, p d = true) ∧
      (∀ d ∈ invDarts X K.secondArc.darts, p d = true) ∧
      IsClosedDartWalk X.toCombMap (K.boundary.cycle.filter p) ∧
      ∃ x ∈ K.boundary.cycle, ∃ y ∈ K.boundary.cycle, p x = true ∧ p y = false ∧
        X.toCombMap.vertexOf x = X.toCombMap.vertexOf y

/-- **The cell pocket step from an in-place move**: the new pocket lives in the same diagram,
between the same cells, with the same arcs, in walk order, with strictly fewer repeated visits. -/
theorem exists_step_of_cellFilterMove (K : CellPocketFaceSet D eps X i j)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) (hmove : CellFilterMove K) :
    ∃ K' : CellPocketFaceSet D eps X i j, K'.ClosedWalk ∧ K'.firstArc = K.firstArc ∧
      K'.secondArc = K.secondArc ∧ K'.repeatedVisits < K.repeatedVisits := by
  obtain ⟨faces, kept, p, hout, hkept, hbd, ht₁, ht₂, hwalk, x, hx, y, hy, hpx, hpy, hxy⟩ := hmove
  have hfilt := filter_cycle_eq_cell K p ht₁ ht₂
  have hperm : List.Perm K.boundary.cycle ((K.firstSide.filter p ++
      invDarts X K.firstArc.darts ++ K.secondSide.filter p ++ invDarts X K.secondArc.darts) ++
      K.boundary.cycle.filter (fun d => !p d)) := by
    rw [← hfilt]
    exact (List.filter_append_perm p K.boundary.cycle).symm
  have hnd : (K.firstSide.filter p ++ invDarts X K.firstArc.darts ++ K.secondSide.filter p ++
      invDarts X K.secondArc.darts).Nodup :=
    (List.nodup_append.mp (K.boundary.cycle_nodup.perm hperm)).1
  have hmem : ∀ d, d ∈ K.firstSide.filter p ++ invDarts X K.firstArc.darts ++
      K.secondSide.filter p ++ invDarts X K.secondArc.darts ↔
      Surgery.MapCollapse.IsBoundaryDart X.toCombMap faces d := by
    intro d
    rw [← hfilt, List.mem_filter, hbd]
  have hx' : x ∈ K.firstSide.filter p ++ invDarts X K.firstArc.darts ++
      K.secondSide.filter p ++ invDarts X K.secondArc.darts := by
    rw [← hfilt]
    exact List.mem_filter.mpr ⟨hx, hpx⟩
  have hy' : y ∈ K.boundary.cycle.filter (fun d => !p d) :=
    List.mem_filter.mpr ⟨hy, by simp [hpy]⟩
  have hwalk' : IsClosedDartWalk X.toCombMap (K.firstSide.filter p ++
      invDarts X K.firstArc.darts ++ K.secondSide.filter p ++ invDarts X K.secondArc.darts) := by
    rw [← hfilt]
    exact hwalk
  obtain ⟨_, hch, hcl⟩ := hwalk'
  have hs₁ : (K.firstSide.filter p).length ≤ eps :=
    (List.length_filter_le p _).trans K.firstSide_length_le
  have hs₂ : (K.secondSide.filter p).length ≤ eps :=
    (List.length_filter_le p _).trans K.secondSide_length_le
  refine ⟨CellPocketFaceSet.ofBoundaryCycle (faces := faces)
      ⟨K.firstSide.filter p ++ invDarts X K.firstArc.darts ++ K.secondSide.filter p ++
        invDarts X K.secondArc.darts, List.ne_nil_of_mem hx', hnd, hmem⟩
      kept K.firstArc K.secondArc (K.firstSide.filter p) (K.secondSide.filter p) rfl hout
      K.firstArc_pos K.secondArc_pos hkept hs₁ hs₂
      ((PocketFaceSet.wordNorm_dartWord_le_length hlabel (K.firstSide.filter p)).trans hs₁)
      ((PocketFaceSet.wordNorm_dartWord_le_length hlabel (K.secondSide.filter p)).trans hs₂),
      ?_, rfl, rfl, ?_⟩
  · exact ⟨hch, hcl⟩
  · unfold CellPocketFaceSet.repeatedVisits
    exact P10Rose.length_sub_card_lt X.toCombMap.vertexOf hperm hx' hy' hxy

/-- **The rose step from an in-place move**, in the form of `CellRoseStepStatement`: the same
diagram, the identity O-equivalence, the same cells, proper arcs. -/
theorem exists_step_of_cellFilterMove'
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hij : i ≠ j)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length) (hmove : CellFilterMove K) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
        K'.secondArc.length < (cellDarts X' j').length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  obtain ⟨K', hK', h₁, h₂, hlt⟩ := exists_step_of_cellFilterMove K hlabel hmove
  refine ⟨X, i, j, K', ⟨OEquivalentDiscDiagram.refl X⟩, hlabel, hij, hK', ?_, ?_, hlt⟩
  · rw [h₁]
    exact hfirst
  · rw [h₂]
    exact hsecond

end Filter

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.filter_cycle_eq_cell
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CellFilterMove
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.exists_step_of_cellFilterMove
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.exists_step_of_cellFilterMove'
