import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Rose
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.Lobe
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: the rose step of the cell pinch from a closed cut

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the cells `Π_i` and `Π_j`.  This module
proves the part of `CellRoseStepStatement` (module `Piece06/Rose`) that happens in the same
diagram, and isolates the rest as `CellRoseUncutStatement`.

## The mathematics

Let `K` be a cell pocket face set of `X` between the cells `i ≠ j`, with boundary cycle
`c = s_1 t̄_1 s_2 t̄_2` in walk order, and write `R` for the face-class relation
`FaceClassStep (walkKeep c)`: move around a face, or cross an edge off `c`.

1. **Repeated visits depend only on the face set.**  The boundary cycle of a face set is determined
   up to order by the face set, so reordering the walk never lowers `repeatedVisits`.  A step must
   change the face set, or the diagram.
2. **The cut** (`exists_step_of_cellCut`).  Suppose `c = A ++ B ++ C`, where
   * the cut sub-walk `B` is nonempty and closed for `R` (every dart of `c` related to a dart of `B`
     lies in `B`),
   * `B` starts at the vertex where the rest `C ++ A` starts,
   * the rest reads `A ++ C = s₁ ++ t̄_1 ++ s₂ ++ t̄_2` with `|s₁|, |s₂| ≤ ε` and the arcs of `K`,
   * some relator cell `k` lies in the lobe of the rest, `lobeFaces c (A ++ C)`.

   By `P10Rose.closed_right` the rest is closed, so by `P10Rose.lobeBoundary` it is the boundary
   cycle of its lobe, which lies in `K.faces` (`P10Rose.mem_faces_of_mem_lobeFaces`): the exterior
   face is off it.  The rotated walk `B ++ (C ++ A)` is a closed dart walk, and its two parts start at
   one vertex, so `C ++ A`, hence `A ++ C`, is a closed dart walk (`P10Rose.closedDartWalk_split`,
   `IsClosedDartWalk.append_comm`).  So `CellPocketFaceSet.ofBoundaryCycle` builds a cell pocket `K'`
   of the same diagram between the same cells, with the arcs of `K` (positive and proper), kept cell
   `k`, in walk order.  With letter labels the side norms are at most the side lengths
   (`PocketFaceSet.wordNorm_dartWord_le_length`).  The first dart of `B` and the first dart of the
   rest start at one vertex, so the repeated visits drop strictly (`P10Rose.length_sub_card_lt`).
   The step is then the identity O-equivalence (`exists_step_of_cellCut'`).
3. **Why the lobe of `B` does not help.**  For outer pockets (`P10Rose.exists_step_of_cut`) the
   relator cell may lie in the lobe of `B`, and `B` alone with empty arcs is a pocket.  A cell pocket
   needs positive arcs (`firstArc_pos`, `secondArc_pos`): both cells must lie across darts of the
   walk.  When `B` lies inside a side it carries no arc darts, so its lobe is not a cell pocket, and
   the cut applies only when a relator cell lies in the lobe of the rest.
4. **The residual** (`CellRoseUncutStatement`).  The rose step with the extra hypothesis that no
   cut as in (2) exists.  `cellRoseStep_of_uncut` recovers `CellRoseStepStatement` by cases on
   `CellCut K`.

## The configurations left in the residual

* *Lakes.*  A component of the complement of `K.faces` away from the exterior touching `∂K`.  Each
  lobe of the walk cut at the pinch vertex shares the face class of a lake edge with another lobe, so
  no lobe is closed.  Filling the lakes (`PocketFaceSet.absorb` for outer pockets) has no cell
  analogue yet, and walk order of the absorbed cycle is not proved.
* *The three petals.*  Petals `P_1` (a G-cell carrying `t_1`), `P_2` (a G-cell carrying `t_2`) and
  `P_k = {kept}` meet at one vertex `v`, with exterior corners between them, and the walk visits them
  in rotation order reversed (`π a = a - 1` in the local model `o_1 ī_1 o_2 ī_2 o_3 ī_3`): every
  passage at `v` is non-first and crossed, `repeatedVisits = 2`.  The only closed cuts are unions of
  petals.  A lobe of a cut without both arcs is not a cell pocket; the lobe of the rest carries both
  arcs only when the cut is `P_k`, and then it carries no relator cell.  So no step exists in the
  same diagram, the exterior corners allow no split surgery, and the step must change the diagram.
  `OEquivalentDiscDiagram` only fixes the boundary word and the relator cell words, so this is not a
  counterexample to `CellRoseStepStatement`; it is the reason the residual is stated over O-equivalent
  copies.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated

section Cut

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **The cell pocket step from a closed cut with a relator cell in the rest.**  The new pocket is
the lobe of the rest of the cycle, in the same diagram, between the same cells, with the same
arcs. -/
theorem exists_step_of_cellCut (K : CellPocketFaceSet D eps X i j)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) (hK : K.ClosedWalk)
    {A B C : List X.toCombMap.Dart} (hc : K.boundary.cycle = A ++ (B ++ C)) (hB : B ≠ [])
    (hrest : C ++ A ≠ [])
    (hv : X.toCombMap.vertexOf (B.head hB) = X.toCombMap.vertexOf ((C ++ A).head hrest))
    (hclosed : ∀ d ∈ B, ∀ e ∈ K.boundary.cycle,
      Relation.EqvGen (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle))
        d e → e ∈ B)
    {s₁ s₂ : List X.toCombMap.Dart}
    (hdec : A ++ C = s₁ ++ invDarts X K.firstArc.darts ++ s₂ ++ invDarts X K.secondArc.darts)
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps) {k : Fin X.rCellCount}
    (hk : (cell X k).face ∈ P10Rose.lobeFaces X.toCombMap K.boundary.cycle (A ++ C)) :
    ∃ K' : CellPocketFaceSet D eps X i j, K'.ClosedWalk ∧ K'.firstArc = K.firstArc ∧
      K'.secondArc = K.secondArc ∧ K'.repeatedVisits < K.repeatedVisits := by
  have hperm : List.Perm K.boundary.cycle (B ++ (A ++ C)) := by
    rw [hc]
    exact List.perm_append_comm_assoc _ _ _
  obtain ⟨-, hndL', -⟩ := List.nodup_append.mp (K.boundary.cycle_nodup.perm hperm)
  have hL' : ∀ d ∈ A ++ C, d ∈ K.boundary.cycle := fun d hd =>
    hperm.mem_iff.mpr (List.mem_append_right _ hd)
  have hy : (C ++ A).head hrest ∈ A ++ C :=
    List.perm_append_comm.mem_iff.mp (List.head_mem hrest)
  have hw0 : IsClosedDartWalk X.toCombMap (A ++ (B ++ C)) := by
    rw [← hc]
    exact ⟨K.boundary.cycle_nonempty, hK.1, hK.2⟩
  have hw1 : IsClosedDartWalk X.toCombMap (B ++ (C ++ A)) := by
    have h := hw0.append_comm
    rwa [List.append_assoc] at h
  obtain ⟨-, hwR⟩ := P10Rose.closedDartWalk_split hw1 hB hrest hv
  have hwL' : IsClosedDartWalk X.toCombMap (A ++ C) := hwR.append_comm
  obtain ⟨_, hch, hcl⟩ := hwL'
  have hclosed' := P10Rose.closed_right hperm K.boundary.cycle_nodup hclosed
  refine ⟨CellPocketFaceSet.ofBoundaryCycle
      (P10Rose.lobeBoundary K.boundary.cycle_mem_iff hL' hclosed' (List.ne_nil_of_mem hy) hndL')
      k K.firstArc K.secondArc s₁ s₂ hdec
      (fun h => K.outerFace_not_mem
        (P10Rose.mem_faces_of_mem_lobeFaces K.boundary.cycle_mem_iff hL' h))
      K.firstArc_pos K.secondArc_pos hk hs₁ hs₂
      ((PocketFaceSet.wordNorm_dartWord_le_length hlabel s₁).trans hs₁)
      ((PocketFaceSet.wordNorm_dartWord_le_length hlabel s₂).trans hs₂), ?_, rfl, rfl, ?_⟩
  · exact ⟨hch, hcl⟩
  · unfold CellPocketFaceSet.repeatedVisits
    exact P10Rose.length_sub_card_lt X.toCombMap.vertexOf (hperm.trans List.perm_append_comm) hy
      (List.head_mem hB) hv.symm

/-- **A closed cut of a cell pocket with a relator cell in the rest**: the data of
`exists_step_of_cellCut`. -/
def CellCut (K : CellPocketFaceSet D eps X i j) : Prop :=
  ∃ (A B C s₁ s₂ : List X.toCombMap.Dart) (hB : B ≠ []) (hrest : C ++ A ≠ [])
    (k : Fin X.rCellCount),
    K.boundary.cycle = A ++ (B ++ C) ∧
      X.toCombMap.vertexOf (B.head hB) = X.toCombMap.vertexOf ((C ++ A).head hrest) ∧
      (∀ d ∈ B, ∀ e ∈ K.boundary.cycle,
        Relation.EqvGen
          (CombMap.FaceClassStep X.toCombMap (walkKeep X.toCombMap K.boundary.cycle)) d e →
          e ∈ B) ∧
      A ++ C = s₁ ++ invDarts X K.firstArc.darts ++ s₂ ++ invDarts X K.secondArc.darts ∧
      s₁.length ≤ eps ∧ s₂.length ≤ eps ∧
      (cell X k).face ∈ P10Rose.lobeFaces X.toCombMap K.boundary.cycle (A ++ C)

/-- **The rose step from a closed cut**, in the form of `CellRoseStepStatement`: the same diagram,
the identity O-equivalence, the same cells. -/
theorem exists_step_of_cellCut' (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hK : K.ClosedWalk) (hij : i ≠ j)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length) (hcut : CellCut K) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
        K'.secondArc.length < (cellDarts X' j').length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  obtain ⟨A, B, C, s₁, s₂, hB, hrest, k, hc, hv, hclosed, hdec, hs₁, hs₂, hk⟩ := hcut
  obtain ⟨K', hK', h₁, h₂, hlt⟩ :=
    exists_step_of_cellCut K hlabel hK hc hB hrest hv hclosed hdec hs₁ hs₂ hk
  refine ⟨X, i, j, K', ⟨OEquivalentDiscDiagram.refl X⟩, hlabel, hij, hK', ?_, ?_, hlt⟩
  · rw [h₁]
    exact hfirst
  · rw [h₂]
    exact hsecond

end Cut

/-- **The rose step of the cell pinch without a closed cut** (OPEN; the residual of gap 6).
`CellRoseStepStatement` with the extra hypothesis `¬ CellCut K`: no closed sub-walk of the boundary
cycle can be cut off while a relator cell stays in the lobe of the rest with both arcs.  This covers
the lakes and the three-petal rose of the module docstring. -/
def CellRoseUncutStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount),
    i ≠ j → X.LeastArea → (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk → ¬ K.FirstTurns →
      K.firstArc.length < (cellDarts X i).length →
      K.secondArc.length < (cellDarts X j).length →
      ¬Unpinched X.toCombMap K.faces → AllNonFirstTurnsCrossed K → ¬ CellCut K →
        ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
          (K' : CellPocketFaceSet D eps X' i' j'),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
            K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
            K'.secondArc.length < (cellDarts X' j').length ∧
            K'.repeatedVisits < K.repeatedVisits

/-- **The rose step of the cell pinch from its uncut residual**: a closed cut performs the step in
the same diagram (`exists_step_of_cellCut'`); otherwise the residual applies. -/
theorem cellRoseStep_of_uncut (h : CellRoseUncutStatement.{u, w, v}) :
    CellRoseStepStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j hij hlea hlabel K hK hnft hfirst hsecond hpinch hrose
  by_cases hcut : CellCut K
  · exact exists_step_of_cellCut' hlabel K hK hij hfirst hsecond hcut
  · exact h D eps X i j hij hlea hlabel K hK hnft hfirst hsecond hpinch hrose hcut

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.exists_step_of_cellCut
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CellCut
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.exists_step_of_cellCut'
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.CellRoseUncutStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.cellRoseStep_of_uncut
