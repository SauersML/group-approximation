import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSubdiagram
import GroupApproximation.Meta.AxiomGuard

/-!
# Enclosed face sets whose outside walk turns to its successor

`EnclosedFaceSet` (`ClosedWalkEnclosedSubdiagram`) asks that at every dart `d` of the outside walk,
rotating from `α d`, the first dart met on an edge of the walk is a walk dart.  That condition does
not fix the order of the walk.  At a vertex carrying three loops, a walk may list the loops out of
rotation order and still pass it, and then the enclosed subdiagram need not be least area: lane
ms-inverses-1's out-of-order model refutes `EnclosedLeastAreaFilterStatement` in this way.

This module adds the successor form, additively: the first dart met is the next dart of the walk.

* `EnclosedFaceSetSucc`: an enclosed face set whose outside walk turns to its successor.
* `ClosedWalkEnclosedSubdiagramSuccStatement` and `EnclosedLeastAreaFilterSuccStatement`: the
  enclosed subdiagram and the singular least-area filter over `EnclosedFaceSetSucc`.
* `leastArea_of_enclosedLeastAreaFilterSucc`: the least-area clause from the filter.
* `closedWalkEnclosedSubdiagramSucc_of_statement` and `enclosedLeastAreaFilterSucc_of_statement`:
  the unsuffixed statements give the successor forms.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemmas 9.4 and 9.7); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **An enclosed face set whose outside walk turns to its successor.**  Besides the fields of
`EnclosedFaceSet`, at every position `i` of the outside walk, rotating from the reverse of the dart at
`i`, the first dart met on an edge of the walk is the dart at the next position. -/
structure EnclosedFaceSetSucc (Delta : DiscDiagram.{u, w, v} W)
    (faces : Finset Delta.toCombMap.Face) (outerWalk : List Delta.toCombMap.Dart) : Prop
    extends EnclosedFaceSet Delta faces outerWalk where
  turn_next : ∀ (i : ℕ) (hi : i < outerWalk.length) (m : ℕ), 0 < m →
    walkKeep Delta.toCombMap outerWalk
      ((Delta.toCombMap.sigma ^ m) (Delta.toCombMap.alpha outerWalk[i])) →
    (∀ k, 0 < k → k < m → ¬ walkKeep Delta.toCombMap outerWalk
      ((Delta.toCombMap.sigma ^ k) (Delta.toCombMap.alpha outerWalk[i]))) →
    (Delta.toCombMap.sigma ^ m) (Delta.toCombMap.alpha outerWalk[i]) =
      outerWalk[(i + 1) % outerWalk.length]'
        (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi))

open scoped Classical in
/-- **The enclosed subdiagram of a closed walk**, over an outside walk that turns to its successor.
The clauses are those of `ClosedWalkEnclosedSubdiagramStatement`. -/
def ClosedWalkEnclosedSubdiagramSuccStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) (faces : Finset Delta.toCombMap.Face)
    (outerWalk : List Delta.toCombMap.Dart), EnclosedFaceSetSucc Delta faces outerWalk →
    ∃ Xi : DiscDiagram.{u, w, v} W,
      Xi.boundaryWord = dartWord Delta (invDarts Delta outerWalk) ∧
      Xi.rCellCount ≤ (Delta.relatorCells.filter fun C => C.face ∈ faces).length ∧
      ((∃ C ∈ Delta.relatorCells, C.face ∈ faces) → 0 < Xi.rCellCount) ∧
      (∃ ι : Fin Xi.rCellCount ↪ Fin Delta.rCellCount, ∀ j : Fin Xi.rCellCount,
        (cell Xi j).word = (cell Delta (ι j)).word ∧ (cell Delta (ι j)).face ∈ faces) ∧
      (Delta.LeastArea → Xi.LeastArea)

open scoped Classical in
/-- **The singular least-area filter**, over an outside walk that turns to its successor.  In a
least-area diagram, a filling of the inverse outside walk needs at least as many relators as the
enclosed face set holds relator cells. -/
def EnclosedLeastAreaFilterSuccStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W), Delta.LeastArea →
    ∀ (faces : Finset Delta.toCombMap.Face) (outerWalk : List Delta.toCombMap.Dart),
      EnclosedFaceSetSucc Delta faces outerWalk →
      ∀ {m : ℕ}, RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) m
          (RelLetter.listVal (dartWord Delta (invDarts Delta outerWalk))) →
        (Delta.relatorCells.filter fun C => C.face ∈ faces).length ≤ m

open scoped Classical in
/-- **The least-area clause from the successor-form filter.** -/
theorem leastArea_of_enclosedLeastAreaFilterSucc
    (hfilter : EnclosedLeastAreaFilterSuccStatement.{u, w, v})
    {Delta : DiscDiagram.{u, w, v} W} (hlea : Delta.LeastArea)
    {faces : Finset Delta.toCombMap.Face} {outerWalk : List Delta.toCombMap.Dart}
    (hE : EnclosedFaceSetSucc Delta faces outerWalk) {Xi : DiscDiagram.{u, w, v} W}
    (hword : Xi.boundaryWord = dartWord Delta (invDarts Delta outerWalk))
    (hcount : Xi.rCellCount ≤ (Delta.relatorCells.filter fun C => C.face ∈ faces).length) :
    Xi.LeastArea := by
  intro m hm
  have hm' : RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) m
      (RelLetter.listVal (dartWord Delta (invDarts Delta outerWalk))) := by
    rw [← hword]
    exact hm
  exact hcount.trans (hfilter Delta hlea faces outerWalk hE hm')

/-- The unsuffixed enclosed subdiagram statement gives the successor form. -/
theorem closedWalkEnclosedSubdiagramSucc_of_statement
    (h : ClosedWalkEnclosedSubdiagramStatement.{u, w, v}) :
    ClosedWalkEnclosedSubdiagramSuccStatement.{u, w, v} := by
  intro G _ Lambda W Delta faces outerWalk hE
  exact h Delta faces outerWalk hE.toEnclosedFaceSet

/-- The unsuffixed filter gives the successor form. -/
theorem enclosedLeastAreaFilterSucc_of_statement (h : EnclosedLeastAreaFilterStatement.{u, w, v}) :
    EnclosedLeastAreaFilterSuccStatement.{u, w, v} := by
  intro G _ Lambda W Delta hlea faces outerWalk hE m hm
  exact h Delta hlea faces outerWalk hE.toEnclosedFaceSet hm

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.EnclosedFaceSetSucc
#audit_axioms GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSubdiagramSuccStatement
#audit_axioms GroupApproximation.GGT.VanKampen.EnclosedLeastAreaFilterSuccStatement
#audit_axioms GroupApproximation.GGT.VanKampen.leastArea_of_enclosedLeastAreaFilterSucc
#audit_axioms GroupApproximation.GGT.VanKampen.closedWalkEnclosedSubdiagramSucc_of_statement
#audit_axioms GroupApproximation.GGT.VanKampen.enclosedLeastAreaFilterSucc_of_statement
