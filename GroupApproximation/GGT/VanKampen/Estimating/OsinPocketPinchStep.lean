import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPinchUnpinched
import GroupApproximation.Meta.AxiomGuard

/-!
# The pinch, one step at a time

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  `PocketPinchLabelledStatement` asks, for a pocket face set in walk order
of a diagram whose labels are letters, for an O-equivalent copy with a simple pocket face set.  A
pocket in walk order on an unpinched face set is already simple: its darts start at distinct
vertices, and a boundary cycle never holds both darts of an edge.  So the pinch follows by
induction from one step that lowers the number of repeated visits, keeping walk order and letter
labels.

* `PocketFaceSet.repeatedVisits`: the darts of the boundary cycle less the vertices they start at.
* `PocketFaceSet.simple_of_closedWalk_of_unpinched`: a pocket in walk order on an unpinched face set
  is simple.
* `PocketPinchStepStatement`: one step of the pinch.
* `pocketPinchLabelledStatement_of_step`: the step gives the labelled pinch, by strong induction on
  the repeated visits.

## Manuscript status

Infrastructure for `thm:hull` (tex 1903,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`); certifies no printed
sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Surgery.MapCollapse

namespace PocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

open Classical in
/-- **The repeated visits of a pocket**: the darts of the boundary cycle less the vertices they
start at. -/
noncomputable def repeatedVisits (K : PocketFaceSet D eps X lo hi) : ℕ :=
  K.boundary.cycle.length - (K.boundary.cycle.map X.toCombMap.vertexOf).toFinset.card

/-- **A pocket in walk order on an unpinched face set is simple.** -/
theorem simple_of_closedWalk_of_unpinched (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (hpinch : Unpinched X.toCombMap K.faces) : K.Simple :=
  (⟨K.boundary.cycle_nonempty, hK.1, hK.2, (K.boundary.unpinched_iff_nodup).mp hpinch,
    fun _ hd had =>
      ((K.boundary.cycle_mem_iff _).mp hd).2 ((K.boundary.cycle_mem_iff _).mp had).1⟩ :
    IsSimpleClosedWalk X.toCombMap K.boundary.cycle)

end PocketFaceSet

/-- **One step of the pinch** (lane `hull-respell`).  A pocket face set in walk order, on a pinched
face set of a diagram whose labels are letters of the symmetrized alphabet, has an O-equivalent
copy whose labels are letters, with a pocket face set in walk order in the same positions and with
fewer repeated visits. -/
def PocketPinchStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ),
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬Unpinched X.toCombMap K.faces →
      ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
        Nonempty (OEquivalentDiscDiagram X X') ∧
          (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
          K'.ClosedWalk ∧ K'.repeatedVisits < K.repeatedVisits

/-- **The pinch, by induction on repeated visits.**  An unpinched pocket in walk order is simple,
with the diagram itself as the copy; a pinched one takes a step and O-equivalences compose. -/
theorem pocketPinchLabelledStatement_of_step (h : PocketPinchStepStatement.{u, w, v}) :
    PocketPinchLabelledStatement.{u, w, v} := by
  intro G _ Lambda D eps W X₀ lo hi hlabel₀ K₀ hK₀
  have H : ∀ (n : ℕ) (X : DiscDiagram.{u, w, v} W),
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
      ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → K.repeatedVisits = n →
        ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
          Nonempty (OEquivalentDiscDiagram X X') ∧ K'.Simple := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih X hlabel K hK hn
    by_cases hpinch : Unpinched X.toCombMap K.faces
    · exact ⟨X, K, ⟨OEquivalentDiscDiagram.refl X⟩, K.simple_of_closedWalk_of_unpinched hK hpinch⟩
    · obtain ⟨X₁, K₁, ⟨e₁⟩, hlabel₁, hK₁, hlt⟩ := h D eps W X lo hi hlabel K hK hpinch
      obtain ⟨X₂, K₂, ⟨e₂⟩, hK₂⟩ :=
        ih K₁.repeatedVisits (lt_of_lt_of_eq hlt hn) X₁ hlabel₁ K₁ hK₁ rfl
      exact ⟨X₂, K₂, ⟨OEquivalentDiscDiagram.trans e₁ e₂⟩, hK₂⟩
  exact H _ X₀ hlabel₀ K₀ hK₀ rfl

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketFaceSet.simple_of_closedWalk_of_unpinched
#audit_axioms GroupApproximation.GGT.VanKampen.pocketPinchLabelledStatement_of_step
