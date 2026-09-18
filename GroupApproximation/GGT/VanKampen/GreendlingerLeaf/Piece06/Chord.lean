import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.Predicate
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellPinchSectionDistinct
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: the split of a cell pocket at an uncrossed turn

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  This module transfers the chord split of an
outer pinch (`Estimating/OsinPocketOuterPinchChord.lean`, stated there for `PocketFaceSet`) to cell
pocket face sets between two distinct cells (step 4 of the plan in `Piece06/Predicate`).

* `closedWalk_of_chordKept`: if every turn of the cycle, and the closing turn, is kept at the split
  (`PinchSplit.Input.ChordKept`), the split cell pocket is a closed walk.
* `exists_step_of_chordKept`: the conclusion of the step under the kept-turn chain and one dart
  running into each split dart without passing the other.
* `exists_step_of_uncrossedTurn`: the conclusion of the step at an uncrossed turn, from the positions
  of `OuterPinchChord.chord_positions`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated OuterPinchChord
open scoped Classical

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **Walk order across a split at an uncrossed turn**, for cell pockets: every turn of the cycle,
and the closing turn, is kept at the split. -/
theorem closedWalk_of_chordKept (K : CellPocketFaceSet D eps X i j)
    (I : PinchSplit.Input X) (hs : I.Avoids K.faces)
    (hchain : K.boundary.cycle.IsChain fun d e => I.ChordKept (X.toCombMap.alpha d) e)
    (hcloses : I.ChordKept
      (X.toCombMap.alpha (K.boundary.cycle.getLast K.boundary.cycle_nonempty))
      (K.boundary.cycle.head K.boundary.cycle_nonempty)) :
    (K.pinchSplit I hs).ClosedWalk :=
  ⟨hchain.imp fun _ _ h => I.vertexOf_eq_of_chordKept h, I.vertexOf_eq_of_chordKept hcloses⟩

/-- **One step of the cell pinch under the kept-turn chain of an uncrossed turn, for distinct
cells.** -/
theorem exists_step_of_chordKept
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hij : i ≠ j)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length)
    (I : PinchSplit.Input X) (hs : I.Avoids K.faces)
    (hchain : K.boundary.cycle.IsChain fun d e => I.ChordKept (X.toCombMap.alpha d) e)
    (hcloses : I.ChordKept
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
    closedWalk_of_chordKept K I hs hchain hcloses, K.pinchSplit_first_proper I hs hfirst,
    K.pinchSplit_second_proper I hs hsecond,
    K.pinchSplit_repeatedVisits_lt_of_stretch I hs he₁ he₂ hn₁ hy₁ hn₂ hx₂⟩

/-- **One step of the cell pinch at an uncrossed turn, for distinct cells.**  For a cell pocket in
walk order with both arcs proper, a split outside the face set at a turn `d₀ → e₀` that no other
passage at its vertex crosses, with `x` reached from `e₀` and `alpha d₀` reached from `y` past darts
off the edges of the cycle, and a dart `z₀` of the cycle at the vertex outside the sector from
`alpha d₀` to `e₀`, gives the conclusion of the step. -/
theorem exists_step_of_uncrossedTurn
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : CellPocketFaceSet D eps X i j) (hK : K.ClosedWalk) (hij : i ≠ j)
    (hfirst : K.firstArc.length < (cellDarts X i).length)
    (hsecond : K.secondArc.length < (cellDarts X j).length)
    (I : PinchSplit.Input X) (hs : I.Avoids K.faces)
    {d₀ e₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle)
    (hnext₀ : K.boundary.cycle.next d₀ hd₀ = e₀)
    (huncross : ∀ d (hd : d ∈ K.boundary.cycle), d ≠ d₀ →
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) →
        (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (X.toCombMap.alpha d) ↔
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (K.boundary.cycle.next d hd)))
    {k₀ m q : ℕ} (hk₀ : (X.toCombMap.sigma ^ k₀) (X.toCombMap.alpha d₀) = e₀)
    (hk₀min : ∀ t, 0 < t → t < k₀ → (X.toCombMap.sigma ^ t) (X.toCombMap.alpha d₀) ≠ e₀)
    (hm : (X.toCombMap.sigma ^ m) e₀ = I.x)
    (hkeepm : ∀ t, 0 < t → t ≤ m →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) e₀))
    (hq0 : 0 < q) (hq : (X.toCombMap.sigma ^ q) I.y = X.toCombMap.alpha d₀)
    (hkeepq : ∀ t, 0 < t → t < q →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) I.y))
    {z₀ : X.toCombMap.Dart} (hz₀ : z₀ ∈ K.boundary.cycle)
    (hz₀v : X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) z₀) (hz₀e : z₀ ≠ e₀)
    (hz₀out : ¬ RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ z₀) :
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
  have hz₀a : z₀ ≠ X.toCombMap.alpha d₀ := fun h => hc d₀ hd₀ (by rw [← h]; exact hz₀)
  obtain ⟨N, -, -, -, hmk, hxpos, hypos, hinj, -, hafter⟩ := chord_positions I hc hd₀ he₀ hk₀
    hk₀min hm hkeepm hq hkeepq (Or.inl hz₀) hz₀v hz₀a hz₀e hz₀out
  obtain ⟨hchain, hcloses⟩ := isChain_of_rel_next K.boundary.cycle_nonempty K.boundary.cycle_nodup
    (R := fun d e => I.ChordKept (X.toCombMap.alpha d) e)
    fun d hd => chordKept_of_uncrossed I K.boundary.cycle_nonempty K.boundary.cycle_nodup hc hK.1
      hK.2 hd₀ hnext₀ huncross hk₀ hk₀min hm hkeepm hq0 hq hkeepq hz₀ hz₀v hz₀e hz₀out hd
  obtain ⟨p, hp, hpN, hz⟩ := hafter z₀ (Or.inl hz₀) hz₀v hz₀a hz₀e hz₀out
  obtain ⟨n₂, hn₂, hx₂⟩ := runsIntoY_of_pos hinj hq0 hxpos hypos hp hpN hz
  obtain ⟨n₁, hn₁, hy₁⟩ := runsIntoX_of_pos hinj hq0 hmk hxpos hypos (Nat.le_add_left _ _) hk₀
  exact exists_step_of_chordKept hlabel K hij hfirst hsecond I hs hchain hcloses he₀ hz₀ hn₁ hy₁
    hn₂ hx₂

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.closedWalk_of_chordKept
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.exists_step_of_chordKept
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.exists_step_of_uncrossedTurn
