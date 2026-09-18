import GroupApproximation.GGT.VanKampen.ClosedWalkEnclosedSubdiagramSuccAssembly
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.Meta.AxiomGuard

/-!
# An all-cells enclosed face set with trivial outer word

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

In a least-area diagram `X` with at least one relator cell, an enclosed face set (successor form)
holding every relator cell of `X` has an outside walk whose inverse word does not read `1`.  The
enclosed subdiagram `Ξ` (`closedWalkEnclosedSubdiagramSucc`) reads the inverse outside walk, holds a
relator cell and has least area.  A trivial boundary value is a relator product with no factors,
which least area bounds below by the positive relator count.

* `false_of_allCells_of_listVal_eq_one`: the refutation.
* `listVal_ne_one_of_allCells`: the same statement in contrapositive form, as a consumer of the
  all-cells disjunct of `GL03BPinch.InnerPocketEnclosedTwoArcCorrected` would use it.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06h

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded

/-- **An all-cells enclosed face set does not read `1`** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121).  In a least-area diagram with a relator cell, an
enclosed face set holding every relator cell, whose inverse outside walk reads `1`, is impossible:
its enclosed subdiagram has least area and a relator cell, but its boundary value is the empty
relator product. -/
theorem false_of_allCells_of_listVal_eq_one
    {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {X : DiscDiagram.{u, w, v} W} (hlea : X.LeastArea) (hpos : 0 < X.rCellCount)
    {faces : Finset X.toCombMap.Face} {outerWalk : List X.toCombMap.Dart}
    (hE : EnclosedFaceSetSucc X faces outerWalk)
    (hall : ∀ C' ∈ X.relatorCells, C'.face ∈ faces)
    (hone : RelLetter.listVal (dartWord X (invDarts X outerWalk)) = 1) : False := by
  obtain ⟨Xi, hword, -, hposXi, -, hleaXi⟩ :=
    closedWalkEnclosedSubdiagramSucc.{u, w, v} X faces outerWalk hE
  have hcell : ∃ C ∈ X.relatorCells, C.face ∈ faces :=
    ⟨cell X ⟨0, hpos⟩, cell_mem X ⟨0, hpos⟩, hall _ (cell_mem X ⟨0, hpos⟩)⟩
  have hval : Xi.boundaryValue = 1 := by
    show RelLetter.listVal Xi.boundaryWord = 1
    rw [hword]
    exact hone
  have h0 : RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) 0 Xi.boundaryValue := by
    rw [hval]
    exact RelatorDefectBudget.IsRelatorProduct.one
  have hXi : Xi.LeastArea := hleaXi hlea
  have hzero : Xi.rCellCount ≤ 0 := hXi h0
  exact Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le (hposXi hcell) hzero)

/-- **The inverse outside walk of an all-cells enclosed face set reads an element other than `1`**
(Osin, proof of Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  The contrapositive of
`false_of_allCells_of_listVal_eq_one`. -/
theorem listVal_ne_one_of_allCells
    {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {X : DiscDiagram.{u, w, v} W} (hlea : X.LeastArea) (hpos : 0 < X.rCellCount)
    {faces : Finset X.toCombMap.Face} {outerWalk : List X.toCombMap.Dart}
    (hE : EnclosedFaceSetSucc X faces outerWalk)
    (hall : ∀ C' ∈ X.relatorCells, C'.face ∈ faces) :
    RelLetter.listVal (dartWord X (invDarts X outerWalk)) ≠ 1 :=
  fun hone => false_of_allCells_of_listVal_eq_one hlea hpos hE hall hone

end GroupApproximation.Full.GL06h

#audit_axioms GroupApproximation.Full.GL06h.false_of_allCells_of_listVal_eq_one
#audit_axioms GroupApproximation.Full.GL06h.listVal_ne_one_of_allCells
