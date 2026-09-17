import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellOuterPinchStep
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketOuterPinchCornerFix
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 06: the outer-pinch step between two distinct cells, vocabulary and proof plan

Target: `CellPocketOuterPinchStepSectionDistinctStatement`
(`Estimating/OsinPocketCellPinchSectionDistinct.lean:92`).  Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b): the subdiagram `Γ_1` with `∂Γ_1 = s_1 t_1 s_2 t_2` between two regions joining the
cells `Π_i` and `Π_j`.

## The claim

Let `K` be a cell pocket face set between distinct cells `i ≠ j` of a least-area diagram `X` with
letter labels.  Suppose the boundary cycle `c = K.boundary.cycle` is a closed walk, is not in
first-turn order, both arcs are proper, and the complement of `K.faces` is pinched.  Then there is
an O-equivalent copy `X'` with letter labels and a cell pocket face set `K'` between distinct cells
of `X'`, in walk order, with both arcs proper and strictly fewer repeated visits.  The thresholds are
`eps0 = 0` and `rho0 = 1`; the hyperbolicity and Osin's condition are not used.

## The proof

Write `σ` for the rotation, `α` for the reversal.  A turn of `c` is a pair `d₀ → e₀ = next d₀`; it
lives at the vertex of `α d₀`, since `c` is a closed walk.

1. **A non-first turn.**  As `K` is not in first-turn order, some turn `d₀ → e₀` is not a first turn
   (`exists_nonFirstTurn`): going round the vertex from `e₀`, some edge of `c` is met before `α d₀`.
2. **Crossed turns.**  The turn is *crossed* (`TurnCrossed`) when another passage `α d → next d` at
   the vertex has exactly one endpoint strictly inside the rotation sector from `α d₀` to `e₀`.
   Either every non-first turn is crossed (`AllNonFirstTurnsCrossed`, the rose case), or some
   non-first turn is uncrossed (`exists_uncrossed_of_not_allCrossed`); in the latter case the
   uncrossing hypothesis of `OuterPinchChord.chordKept_of_uncrossed` holds
   (`huncross_of_not_turnCrossed`).
3. **The dart outside the sector.**  At an uncrossed non-first turn,
   `OuterPinchCorners.exists_outside_of_not_firstTurn` gives a dart `z₀ ∈ c` at the vertex, other than
   `e₀`, outside the sector from `α d₀` to `e₀`.
4. **The split.**  Choose `x = σ^m e₀` in the sector after `e₀` and `y` with `σ^q y = α d₀` in the
   sector before `α d₀` (`0 < q`), passing no edge of `c`.  When the corner faces `face (α x)` and
   `face (α y)` are distinct, off the exterior, off the relator cells and off `K.faces`, they form a
   `PinchSplit.Input` avoiding `K.faces` (`exists_input`).  By
   `OuterPinchChord.chord_positions` the positions along the rotation cycle of `α d₀` are
   `e₀` at `k₀`, `x` at `m + k₀`, `y` at `N - q`, and `z₀` strictly after `x`, no later than `y`.  Every
   turn of `c` is kept (`chordKept_of_uncrossed`), so the split cell pocket
   `K.pinchSplit I hs` is a closed walk (`closedWalk_of_chordKept`).  The dart `e₀` runs into `x`
   without passing `y`, and `z₀` runs into `y` without passing `x` (`runsIntoX_of_pos`,
   `runsIntoY_of_pos`), so the repeated visits drop
   (`CellPocketFaceSet.pinchSplit_repeatedVisits_lt_of_stretch`).  The split carries both cells, both
   arcs and the relator words: both arcs stay proper (`pinchSplit_first_proper`,
   `pinchSplit_second_proper`) and the cell indices stay distinct (`indexEquiv.injective`).  Labels
   stay letters and the split is an O-equivalence.  This is `exists_step_of_goodSector` (module
   `Piece06/GoodCorners`); `m = 0`, `q = 1`, `x = e₀`, `y = σ⁻¹ (α d₀)` gives the case of good turn
   corners (`GoodTurnCorners`, `exists_step_of_goodCorners`), where the corner faces are
   `face (α e₀)` and `face (α (σ⁻¹ (α d₀))) = face (α d₀)`; both are off `K.faces` since `e₀` and
   `d₀` are boundary darts.
5. **Bad corners** (module `Piece06/Residual`).  When no choice of `x` and `y` in the two sectors has
   good corners, a corner face is the exterior, a relator cell (for instance the cell `i` when `e₀`
   lies on the reversed first arc), or the two sectors share one face.  The intended repair doubles an
   edge of the offending face outside `K.faces` (`CellPocketFaceSet.faceEdgeDoubling`, or
   `exists_trimDoubleFirst` / `exists_trimDoubleSecond` for an arc corner), which puts a G-digon off
   the exterior into the corner and keeps walk order, repeated visits and proper arcs.  The transport of
   the turn data (`NonFirstTurn`, `¬ TurnCrossed`) across the doubling is not in the library, and an
   exterior corner on both sides admits no split surgery.  This case is a best attempt.
6. **The rose** (module `Piece06/Residual`).  Every non-first turn is crossed.  At a vertex visited
   three times with incoming and outgoing edges alternating as `i₁ o₁ i₂ o₂ i₃ o₃`, the turns
   `i₁ → o₂`, `i₂ → o₃`, `i₃ → o₁` pairwise cross.  No split of the vertex into two σ-intervals keeps
   all three turns, so the step must first reorder the walk, and the side bounds of
   `CellPocketFaceSet` constrain that.  This case is a best attempt.

## This module

* `TurnCrossed`, `NonFirstTurn`, `AllNonFirstTurnsCrossed`, `GoodTurnCorners`: the vocabulary.
* `exists_nonFirstTurn`, `exists_uncrossed_of_not_allCrossed`, `huncross_of_not_turnCrossed`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides OuterPinchIsolated

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount}

/-- **A crossed turn.**  Another passage `alpha d → next d` at the vertex of `alpha d₀` has exactly
one endpoint strictly inside the rotation sector from `alpha d₀` to `next d₀`. -/
def TurnCrossed (K : CellPocketFaceSet D eps X i j) (d₀ : X.toCombMap.Dart)
    (hd₀ : d₀ ∈ K.boundary.cycle) : Prop :=
  ∃ (d : X.toCombMap.Dart) (hd : d ∈ K.boundary.cycle), d ≠ d₀ ∧
    X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) ∧
    ¬ (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (X.toCombMap.alpha d) ↔
        RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (K.boundary.cycle.next d hd))

/-- **A non-first turn** of the boundary cycle. -/
def NonFirstTurn (K : CellPocketFaceSet D eps X i j) (d₀ : X.toCombMap.Dart)
    (hd₀ : d₀ ∈ K.boundary.cycle) : Prop :=
  ¬ FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
    (X.toCombMap.alpha (K.boundary.cycle.next d₀ hd₀)) (X.toCombMap.alpha d₀)

/-- **The rose configuration**: every non-first turn is crossed. -/
def AllNonFirstTurnsCrossed (K : CellPocketFaceSet D eps X i j) : Prop :=
  ∀ (d₀ : X.toCombMap.Dart) (hd₀ : d₀ ∈ K.boundary.cycle),
    NonFirstTurn K d₀ hd₀ → TurnCrossed K d₀ hd₀

/-- **Good corners at a turn `d₀ → e₀`**: the corner faces after `e₀` and before `alpha d₀` are
distinct, off the exterior and off the relator cells. -/
def GoodTurnCorners (X : DiscDiagram.{u, w, v} W) (d₀ e₀ : X.toCombMap.Dart) : Prop :=
  X.toCombMap.faceOf (X.toCombMap.alpha e₀) ≠ X.toCombMap.faceOf (X.toCombMap.alpha d₀) ∧
    X.toCombMap.faceOf (X.toCombMap.alpha e₀) ≠ X.outerFace ∧
    X.toCombMap.faceOf (X.toCombMap.alpha d₀) ≠ X.outerFace ∧
    (∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf (X.toCombMap.alpha e₀)) ∧
    ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf (X.toCombMap.alpha d₀)

/-- A cell pocket not in first-turn order has a non-first turn. -/
theorem exists_nonFirstTurn {K : CellPocketFaceSet D eps X i j} (h : ¬ K.FirstTurns) :
    ∃ (d₀ : X.toCombMap.Dart) (hd₀ : d₀ ∈ K.boundary.cycle), NonFirstTurn K d₀ hd₀ := by
  by_contra hno
  refine h (isChain_of_rel_next K.boundary.cycle_nonempty K.boundary.cycle_nodup
    (R := fun d e => FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
      (X.toCombMap.alpha e) (X.toCombMap.alpha d)) fun d hd => ?_)
  by_contra hnf
  exact hno ⟨d, hd, hnf⟩

/-- Outside the rose configuration some non-first turn is not crossed. -/
theorem exists_uncrossed_of_not_allCrossed {K : CellPocketFaceSet D eps X i j}
    (h : ¬ AllNonFirstTurnsCrossed K) :
    ∃ (d₀ : X.toCombMap.Dart) (hd₀ : d₀ ∈ K.boundary.cycle),
      NonFirstTurn K d₀ hd₀ ∧ ¬ TurnCrossed K d₀ hd₀ := by
  by_contra hno
  refine h fun d₀ hd₀ hnf => ?_
  by_contra hnc
  exact hno ⟨d₀, hd₀, hnf, hnc⟩

/-- **An uncrossed turn** satisfies the uncrossing hypothesis of the chord split. -/
theorem huncross_of_not_turnCrossed {K : CellPocketFaceSet D eps X i j} {d₀ : X.toCombMap.Dart}
    {hd₀ : d₀ ∈ K.boundary.cycle} (h : ¬ TurnCrossed K d₀ hd₀) :
    ∀ (d : X.toCombMap.Dart) (hd : d ∈ K.boundary.cycle), d ≠ d₀ →
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) →
        (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
            (X.toCombMap.alpha d) ↔
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
            (K.boundary.cycle.next d hd)) :=
  fun d hd hne hv => Classical.byContradiction fun hno => h ⟨d, hd, hne, hv, hno⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.exists_nonFirstTurn
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.exists_uncrossed_of_not_allCrossed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece06.huncross_of_not_turnCrossed
