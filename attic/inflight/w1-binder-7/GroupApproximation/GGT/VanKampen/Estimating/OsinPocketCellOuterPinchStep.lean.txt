import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPinchSplit
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPinchIsolated
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchSectionDistinct
import GroupApproximation.Meta.AxiomGuard

/-!
# The pinch step between two cells, at an isolated turn outside the face set

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the cells `Π_i` and `Π_j`.  A cell pocket in walk
order that is not in first-turn order has its complement pinched at a vertex of the walk, and the step
splits that vertex outside the face set at an isolated turn (`PinchSplit.Input.TurnKept`,
`Estimating/OsinPocketOuterPinchSplit.lean`; the positions on the rotation cycle are the list-level
lemmas of `Estimating/OsinPocketOuterPinchIsolated.lean`, lane `w1-binder-3`).  The split carries both
cells, the relator words, the arcs and the sides, so it keeps both arcs proper and the two cells
distinct.

* `CellPocketFaceSet.pinchSplit_first_proper`, `pinchSplit_second_proper`: both arcs stay proper.
* `CellPocketFaceSet.pinchSplit_closedWalk_of_isolated`: walk order when every turn is kept.
* `CellPocketFaceSet.exists_cellPinchStepDistinct_of_isolated`: the conclusion of
  `CellPocketOuterPinchStepSectionDistinctStatement` at such a split.
* `CellPocketFaceSet.exists_cellPinchStepDistinct_of_isolatedTurn`: the same, from the positions of an
  isolated turn `d₀ → e₀` and another dart of the cycle at its vertex.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated
open scoped Classical

namespace CellPocketFaceSet

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A split avoiding the face set keeps the first arc proper.** -/
theorem pinchSplit_first_proper (K : CellPocketFaceSet D eps X i j) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) (hfirst : K.firstArc.length < (cellDarts X i).length) :
    (K.pinchSplit I hs).firstArc.length < (cellDarts I.diagram (I.cellMap.indexEquiv i)).length := by
  have h1 : (K.pinchSplit I hs).firstArc.length = K.firstArc.length :=
    K.firstArc.mapTo_length id (I.cellDarts_eq i)
  have h2 : (cellDarts I.diagram (I.cellMap.indexEquiv i)).length = (cellDarts X i).length :=
    (congrArg List.length (I.cellDarts_eq i)).trans (List.length_map _)
  exact lt_of_eq_of_lt h1 (lt_of_lt_of_eq hfirst h2.symm)

/-- **A split avoiding the face set keeps the second arc proper.** -/
theorem pinchSplit_second_proper (K : CellPocketFaceSet D eps X i j) (I : PinchSplit.Input X)
    (hs : I.Avoids K.faces) (hsecond : K.secondArc.length < (cellDarts X j).length) :
    (K.pinchSplit I hs).secondArc.length <
      (cellDarts I.diagram (I.cellMap.indexEquiv j)).length := by
  have h1 : (K.pinchSplit I hs).secondArc.length = K.secondArc.length :=
    K.secondArc.mapTo_length id (I.cellDarts_eq j)
  have h2 : (cellDarts I.diagram (I.cellMap.indexEquiv j)).length = (cellDarts X j).length :=
    (congrArg List.length (I.cellDarts_eq j)).trans (List.length_map _)
  exact lt_of_eq_of_lt h1 (lt_of_lt_of_eq hsecond h2.symm)

/-- **Walk order across a split at an isolated turn**: every turn of the cycle, and the closing
turn, is kept at the split. -/
theorem pinchSplit_closedWalk_of_isolated (K : CellPocketFaceSet D eps X i j)
    (I : PinchSplit.Input X) (hs : I.Avoids K.faces)
    (hchain : K.boundary.cycle.IsChain fun d e => I.TurnKept (X.toCombMap.alpha d) e)
    (hcloses : I.TurnKept
      (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty))
      (K.boundary.cycle.head K.boundary.cycle_nonempty)) :
    (K.pinchSplit I hs).ClosedWalk :=
  ⟨hchain.imp fun _ _ h => I.vertexOf_eq_of_turnKept h, I.vertexOf_eq_of_turnKept hcloses⟩

/-- **One step of the cell pinch at an isolated turn outside the face set, for distinct cells.**  The
merged faces lie off the face set, every turn of the cycle is kept at the split, one cycle dart runs
into `x` without passing `y` and another into `y` without passing `x`.  The split keeps letter labels,
walk order, both proper arcs and distinct cells, and lowers the repeated visits. -/
theorem exists_cellPinchStepDistinct_of_isolated
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hij : i ≠ j)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length)
    (I : PinchSplit.Input X) (hs : I.Avoids K.faces)
    (hchain : K.boundary.cycle.IsChain fun d e => I.TurnKept (X.toCombMap.alpha d) e)
    (hcloses : I.TurnKept
      (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty))
      (K.boundary.cycle.head K.boundary.cycle_nonempty))
    {e₁ e₂ : X.toCombMap.Dart} (he₁ : e₁ ∈ K.boundary.cycle) (he₂ : e₂ ∈ K.boundary.cycle)
    {n₁ n₂ : ℕ} (hn₁ : (X.toCombMap.sigma ^ n₁) e₁ = I.x)
    (hy₁ : ∀ i ≤ n₁, (X.toCombMap.sigma ^ i) e₁ ≠ I.y)
    (hn₂ : (X.toCombMap.sigma ^ n₂) e₂ = I.y)
    (hx₂ : ∀ i ≤ n₂, (X.toCombMap.sigma ^ i) e₂ ≠ I.x) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
        K'.secondArc.length < (cellDarts X' j').length ∧
        K'.repeatedVisits < K.repeatedVisits :=
  ⟨I.diagram, I.cellMap.indexEquiv i, I.cellMap.indexEquiv j, K.pinchSplit I hs, ⟨I.oEquivalent⟩,
    I.label_isLetter (symmetricLabelAlphabet D) hlabel, I.cellMap.indexEquiv.injective.ne hij,
    K.pinchSplit_closedWalk_of_isolated I hs hchain hcloses, K.pinchSplit_first_proper I hs hfirst,
    K.pinchSplit_second_proper I hs hsecond,
    K.pinchSplit_repeatedVisits_lt_of_stretch I hs he₁ he₂ hn₁ hy₁ hn₂ hx₂⟩

/-- **One step of the cell pinch at an isolated turn, for distinct cells.**  For a cell pocket in walk
order with both arcs proper, a split outside the face set at an isolated turn `d₀ → e₀`, with `x`
reached from `e₀` and `alpha d₀` reached from `y` past darts off the edges of the cycle, and another
dart `z₀` of the cycle at the vertex, gives the conclusion of the step. -/
theorem exists_cellPinchStepDistinct_of_isolatedTurn
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hK : K.ClosedWalk) (hij : i ≠ j)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length)
    (I : PinchSplit.Input X) (hs : I.Avoids K.faces)
    {d₀ e₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle)
    (hnext₀ : K.boundary.cycle.next d₀ hd₀ = e₀)
    {k₀ m q : ℕ} (hk₀ : (X.toCombMap.sigma ^ k₀) (X.toCombMap.alpha d₀) = e₀)
    (hkeep₀ : ∀ t, 0 < t → t < k₀ →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) (X.toCombMap.alpha d₀)))
    (hm : (X.toCombMap.sigma ^ m) e₀ = I.x)
    (hkeepm : ∀ t, 0 < t → t ≤ m →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) e₀))
    (hq0 : 0 < q) (hq : (X.toCombMap.sigma ^ q) I.y = X.toCombMap.alpha d₀)
    (hkeepq : ∀ t, 0 < t → t < q →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) I.y))
    {z₀ : X.toCombMap.Dart} (hz₀ : z₀ ∈ K.boundary.cycle)
    (hz₀v : X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) z₀) (hz₀e : z₀ ≠ e₀) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (i' j' : Fin X'.rCellCount)
      (K' : CellPocketFaceSet D eps X' i' j'),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧ i' ≠ j' ∧
        K'.ClosedWalk ∧ K'.firstArc.length < (cellDarts X' i').length ∧
        K'.secondArc.length < (cellDarts X' j').length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  have hc : ∀ d ∈ K.boundary.cycle, X.toCombMap.alpha d ∉ K.boundary.cycle :=
    fun d hd => K.boundary_alpha_not_mem hd
  have he₀ : e₀ ∈ K.boundary.cycle := by
    rw [← hnext₀]
    exact List.next_mem ..
  have hz₀k : walkKeep X.toCombMap K.boundary.cycle z₀ := Or.inl hz₀
  have hz₀a : z₀ ≠ X.toCombMap.alpha d₀ := fun h => hc d₀ hd₀ (by rw [← h]; exact hz₀)
  obtain ⟨hchain, hcloses⟩ := isChain_of_rel_next K.boundary.cycle_nonempty K.boundary.cycle_nodup
    (R := fun d e => I.TurnKept (X.toCombMap.alpha d) e)
    fun d hd => turnKept_of_isolated I K.boundary.cycle_nonempty K.boundary.cycle_nodup hc hK.1
      hK.2 hd₀ hnext₀ hk₀ hkeep₀ hm hkeepm hq0 hq hkeepq hz₀ hz₀v hz₀e hd
  obtain ⟨n₂, hn₂, hx₂⟩ := runsIntoY_of_isolated I hc hd₀ he₀ hk₀ hkeep₀ hm hkeepm hq0 hq hkeepq
    hz₀k hz₀v hz₀a hz₀e hz₀k hz₀v hz₀a hz₀e
  exact K.exists_cellPinchStepDistinct_of_isolated hlabel hij hfirst hsecond I hs hchain hcloses he₀
    hz₀ hm (runsIntoX_of_isolated I hc hd₀ he₀ hk₀ hkeep₀ hm hkeepm hq0 hq hkeepq hz₀k hz₀v hz₀a hz₀e)
    hn₂ hx₂

end CellPocketFaceSet

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.pinchSplit_first_proper
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.pinchSplit_second_proper
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.pinchSplit_closedWalk_of_isolated
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.exists_cellPinchStepDistinct_of_isolated
#audit_axioms GroupApproximation.GGT.VanKampen.CellPocketFaceSet.exists_cellPinchStepDistinct_of_isolatedTurn
