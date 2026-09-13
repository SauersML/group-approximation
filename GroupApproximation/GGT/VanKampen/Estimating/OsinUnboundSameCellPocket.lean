import GroupApproximation.GGT.VanKampen.RelativeGreendlinger
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.Meta.AxiomGuard

/-!
# Same-cell unbound darts: the pocket value binder

Osin (math/0411039v3, §9), proof of Lemma 9.4.  Take an unbound dart `d` of a relator cell `i`
whose reverse also lies on cell `i`.  Its edge has cell `i` on both sides, so it is a bridge of
the planar map.  The cell walk strictly between `d` and its reverse runs around the side of the
edge away from the exterior.  That side is the pocket.

`OsinLemma94SameCellPocketInput` is the pocket value clause (C) of the site 5 ruling.  At
`C`-parameters the pocket word has value one.

* If the pocket carries no relator cell, the pocket word is the boundary word of a subdiagram
  of `G`-faces.
* Otherwise the pocket gives a loop cut, and the loop cut contradicts Lemma 9.7 on the smaller
  diagram.  The inline binder is the induction hypothesis of `OsinLemma94SectionStatement`.

`AvoidEdgeStep M d` is an elementary dart move that does not cross the edge of `d`.  The
orientation hypothesis says that the start of `d` reaches the exterior by such moves.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

/-- An elementary dart move that does not cross the edge of `d`: a vertex rotation, or an edge
reversal at another edge. -/
def AvoidEdgeStep (M : CombMap) (d x y : M.Dart) : Prop :=
  M.sigma x = y ∨ (x ≠ d ∧ x ≠ M.alpha d ∧ M.alpha x = y)

/-- A move that avoids an edge is an elementary move of the map. -/
theorem AvoidEdgeStep.adjacent {M : CombMap} {d x y : M.Dart} (h : AvoidEdgeStep M d x y) :
    M.Adjacent x y := by
  rcases h with h | ⟨-, -, h⟩
  · exact Or.inr h
  · exact Or.inl h

/-- **The pocket value clause (C).**  At `C`-parameters, with Lemma 9.7 on diagrams with fewer
relator cells in scope, take a dart `d` of cell `i` whose reverse lies on cell `i` and whose
start reaches the exterior without crossing its edge.  The cell word strictly between `d` and
its reverse has value one. -/
def OsinLemma94SameCellPocketInput : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∀ eps : ℕ,
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
            ∀ Delta : DiscDiagram.{u, w, v} W, Delta.LeastArea →
              (∀ (Xi : DiscDiagram.{u, w, v} W)
                  (cutsXi : SectionCuts D lambda c Xi.boundaryWord),
                Xi.LeastArea → 0 < Xi.rCellCount → Xi.rCellCount < Delta.rCellCount →
                  ∃ T : RealizedSectionFamily D lambda c eps Xi cutsXi,
                    OsinLemma97bConclusion mu T) →
              ∀ (i : Fin Delta.rCellCount) (d : Delta.toCombMap.Dart),
                d ∈ cellDarts Delta i →
                Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = (cell Delta i).face →
                (∃ o : Delta.toCombMap.Dart, Delta.toCombMap.faceOf o = Delta.outerFace ∧
                  Relation.EqvGen (AvoidEdgeStep Delta.toCombMap d) d o) →
                ∀ m : ℕ, m + 1 < (cellDarts Delta i).length →
                  (Delta.toCombMap.facePerm ^ (m + 1)) d = Delta.toCombMap.alpha d →
                    RelLetter.listVal (dartWord Delta
                      ((List.range m).map fun t => (Delta.toCombMap.facePerm ^ (t + 1)) d)) = 1

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.AvoidEdgeStep.adjacent
