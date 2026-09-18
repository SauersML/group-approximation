import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.PlaceSides
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.NoBubLists
import GroupApproximation.Meta.AxiomGuard

/-!
# Placement of a non-bubble block on the two arcs of a pocket

Lane gl-p10-58.  The list lemmas of `NoBubLists`, specialised to the boundary cycle
`firstSide ++ invDarts X sourceArc.darts ++ secondSide ++ targetArc.darts` of a pocket face set
and the move predicate of an arbitrary colouring `z`:

* `roseLobeNoBub_place1`: the reversed source arc filters to an infix of itself;
* `roseLobeNoBub_place2`: the target arc filters to a prefix of itself, hence to a prefix of its
  drop by `k = 0` (no wrap condition is needed).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open P10RoseExtremalTrim

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **Source placement of a non-bubble block**: the kept darts of the reversed source arc form an
infix of it, when the whole complement of the block is removed, or a dart of `B` is off the arc,
or `B` is a prefix or a suffix of the arc. -/
theorem roseLobeNoBub_place1 (K : PocketFaceSet D eps X lo hi)
    {z : X.toCombMap.Dart → Bool} {A B C : List X.toCombMap.Dart}
    (hABC : K.boundary.cycle = A ++ B ++ C)
    (hblk : (B.filter (movePred X.toCombMap z) = [] ∧
        (A ++ C).filter (movePred X.toCombMap z) = A ++ C ∧ A ++ C ≠ []) ∨
      (B.filter (movePred X.toCombMap z) = B ∧
        (A ++ C).filter (movePred X.toCombMap z) = [] ∧ B ≠ []))
    (hpos : (A ++ C).filter (movePred X.toCombMap z) = [] ∨
      (∃ d ∈ B, d ∉ invDarts X K.sourceArc.darts) ∨
      B <+: invDarts X K.sourceArc.darts ∨ B <:+ invDarts X K.sourceArc.darts) :
    (invDarts X K.sourceArc.darts).filter (movePred X.toCombMap z) <:+:
      invDarts X K.sourceArc.darts := by
  have h : K.firstSide ++ invDarts X K.sourceArc.darts ++
      (K.secondSide ++ K.targetArc.darts) = A ++ B ++ C := by
    rw [← List.append_assoc, ← K.decomposition, hABC]
  exact roseLobeNoBub_src h (by rw [← hABC]; exact K.boundary.cycle_nodup) hblk hpos

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeNoBub_place1

/-- **Target placement of a non-bubble block, with `k = 0`**: the kept darts of the target arc
form a prefix of it, when no dart of `B` is on the arc, or the removed block ends the cycle, or the
block is kept and no dart of `A` is on the arc. -/
theorem roseLobeNoBub_place2 (K : PocketFaceSet D eps X lo hi)
    {z : X.toCombMap.Dart → Bool} {A B C : List X.toCombMap.Dart}
    (hABC : K.boundary.cycle = A ++ B ++ C)
    (hblk : (B.filter (movePred X.toCombMap z) = [] ∧
        (A ++ C).filter (movePred X.toCombMap z) = A ++ C ∧ A ++ C ≠ []) ∨
      (B.filter (movePred X.toCombMap z) = B ∧
        (A ++ C).filter (movePred X.toCombMap z) = [] ∧ B ≠ []))
    (hpos : (∀ d ∈ B, d ∉ K.targetArc.darts) ∨
      (C = [] ∧ B.filter (movePred X.toCombMap z) = []) ∨
      ((A ++ C).filter (movePred X.toCombMap z) = [] ∧ ∀ d ∈ A, d ∉ K.targetArc.darts)) :
    ∃ k, K.targetArc.start.1 + k ≤ (outerDarts X).length ∧
      K.targetArc.darts.filter (movePred X.toCombMap z) <+: K.targetArc.darts.drop k := by
  have h : K.firstSide ++ invDarts X K.sourceArc.darts ++ K.secondSide ++ K.targetArc.darts =
      A ++ B ++ C := by
    rw [← K.decomposition, hABC]
  refine ⟨0, ?_, ?_⟩
  · have := K.targetArc.start.isLt
    omega
  · rw [List.drop_zero]
    exact roseLobeNoBub_tgt h hblk hpos

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeNoBub_place2

end Pocket

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
