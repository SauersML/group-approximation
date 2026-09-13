import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellFaceSet
import GroupApproximation.Meta.AxiomGuard

/-!
# The pinch between two cells, one step at a time

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the cells `Π_i` and `Π_j`.

`CellPocketPinchPosStatement` (`Estimating/OsinPocketCellFaceSet.lean`) asks, for a cell pocket
face set in walk order of a diagram whose labels are letters, at `ε > 0`, for an O-equivalent copy
with letter labels and a simple cell pocket face set.  As for section pockets
(`Estimating/OsinPocketPinchStep.lean`, `Estimating/OsinPocketPinchPositive.lean`), a cell pocket
in walk order on an unpinched face set is already simple, so the pinch follows by induction from
one step that lowers the number of repeated visits, keeping walk order and letter labels.

* `CellPocketFaceSet.repeatedVisits`: the darts of the boundary cycle less the vertices they start
  at.
* `CellPocketFaceSet.simple_of_closedWalk_of_unpinched`: a cell pocket in walk order on an
  unpinched face set is simple.
* `CellPocketPinchStepPosStatement`: one step of the pinch at `ε > 0`.  The step may change the
  diagram, both cells, the kept cell, the arcs and the sides.
* `cellPocketPinchPosStatement_of_stepPos`: the step gives the pinch, by strong induction on the
  repeated visits.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(b);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Surgery.MapCollapse

namespace CellPocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

open Classical in
/-- **The repeated visits of a cell pocket**: the darts of the boundary cycle less the vertices
they start at. -/
noncomputable def repeatedVisits (K : CellPocketFaceSet D eps X i j) : ℕ :=
  K.boundary.cycle.length - (K.boundary.cycle.map X.toCombMap.vertexOf).toFinset.card

/-- **A cell pocket in walk order on an unpinched face set is simple.** -/
theorem simple_of_closedWalk_of_unpinched (K : CellPocketFaceSet D eps X i j) (hK : K.ClosedWalk)
    (hpinch : Unpinched X.toCombMap K.faces) : K.Simple :=
  (⟨K.boundary.cycle_nonempty, hK.1, hK.2, (K.boundary.unpinched_iff_nodup).mp hpinch,
    fun _ hd had =>
      ((K.boundary.cycle_mem_iff _).mp hd).2 ((K.boundary.cycle_mem_iff _).mp had).1⟩ :
    IsSimpleClosedWalk X.toCombMap K.boundary.cycle)

end CellPocketFaceSet

/-- **One step of the pinch between two cells, at a positive side bound.**  A cell pocket face set
in walk order, on a pinched face set of a diagram whose labels are letters, with side bound
`ε > 0`, has an O-equivalent copy whose labels are letters, with a cell pocket face set in walk
order and fewer repeated visits. -/
def CellPocketPinchStepPosStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ), 0 < eps →
    ∀ (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W)
      (i j : Fin X.rCellCount),
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk → ¬Unpinched X.toCombMap K.faces →
        ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
          (K' : CellPocketFaceSet D eps X' i' j'),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
            K'.ClosedWalk ∧ K'.repeatedVisits < K.repeatedVisits

/-- **The pinch between two cells, by induction on repeated visits.**  An unpinched cell pocket in
walk order is simple, with the diagram itself as the copy; a pinched one takes a step, at the same
side bound, and O-equivalences compose. -/
theorem cellPocketPinchPosStatement_of_stepPos (h : CellPocketPinchStepPosStatement.{u, w, v}) :
    CellPocketPinchPosStatement.{u, w, v} := by
  intro G _ Lambda D eps heps W X₀ i₀ j₀ hlabel₀ K₀ hK₀
  have H : ∀ (n : ℕ) (X : DiscDiagram.{u, w, v} W) (i j : Fin X.rCellCount),
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : CellPocketFaceSet D eps X i j, K.ClosedWalk → K.repeatedVisits = n →
        ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
          (K' : CellPocketFaceSet D eps X' i' j'),
          Nonempty (OEquivalentDiscDiagram X X') ∧
            (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ K'.Simple := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih X i j hlabel K hK hn
    by_cases hpinch : Unpinched X.toCombMap K.faces
    · exact ⟨X, i, j, K, ⟨OEquivalentDiscDiagram.refl X⟩, hlabel,
        K.simple_of_closedWalk_of_unpinched hK hpinch⟩
    · obtain ⟨X₁, i₁, j₁, K₁, ⟨e₁⟩, hlabel₁, hK₁, hlt⟩ := h D eps heps W X i j hlabel K hK hpinch
      obtain ⟨X₂, i₂, j₂, K₂, ⟨e₂⟩, hlabel₂, hK₂⟩ :=
        ih K₁.repeatedVisits (lt_of_lt_of_eq hlt hn) X₁ i₁ j₁ hlabel₁ K₁ hK₁ rfl
      exact ⟨X₂, i₂, j₂, K₂, ⟨OEquivalentDiscDiagram.trans e₁ e₂⟩, hlabel₂, hK₂⟩
  exact H _ X₀ i₀ j₀ hlabel₀ K₀ hK₀ rfl

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.simple_of_closedWalk_of_unpinched
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketPinchStepPosStatement
#audit_axioms GroupApproximation.GGT.VanKampen.cellPocketPinchPosStatement_of_stepPos
