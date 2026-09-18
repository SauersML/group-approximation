import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeAssembly
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueCellTransport
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarStripStep
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixO52LeastArea
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionMultipleEdge
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionInduction
import GroupApproximation.GGT.VanKampen.Estimating.Assembly
import GroupApproximation.Meta.AxiomGuard

/-!
# A pocket with two arcs outside, refuted below the inductive bound

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

A pocket region of an O-equivalent copy, with both cycles following their boundaries, a relator
cell inside and two cells `Π_i'`, `Π_j'` outside, whose inverse complement cycle reads
`s_1 A_1⁻¹ s_2 A_2⁻¹` with side values of norm at most `ε`, is a multiple-edge cut of `X`
with fewer relator cells.  Clause (b) below the relator count of `X` refutes it.

* `TwoArcExit`: the exit shape.
* `TwoArcExit.of_oEquivalent`: an exit of an O-equivalent copy is an exit of `X`.
* `false_of_twoArcExit`: the refutation, from `nonempty_osinMultipleEdgeCut_of_pocketRegion`
  (closed collar `GeodesicCollar.StripStep.geodesicCollarStatement_holds` and cell transport
  `pocketCellTransport`) and `OsinMultipleEdgeCut.false_of_below` (with `o52LeastArea`).

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06g

universe u w v

open GroupApproximation.GGT GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded

section Exit

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A pocket with two arcs outside** (Osin, proof of Lemma 9.7(b); `thm:hull`).  A pocket
region of an O-equivalent copy with letter labels, both cycles following their boundaries, holding
a relator cell, with cells `Π_i'`, `Π_j'` off it, whose inverse complement cycle reads
`s_1 A_1⁻¹ s_2 A_2⁻¹`, the side values of norm at most `ε`. -/
def TwoArcExit (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) : Prop :=
  ∃ (X' : DiscDiagram.{u, w, v} W) (P : PocketRegion X')
    (C : RelatorCell X'.toCombMap X'.outerFace W) (i' j' : Fin X'.rCellCount)
    (A₁ : CyclicArc (cellDarts X' i')) (A₂ : CyclicArc (cellDarts X' j'))
    (s₁ s₂ : List X'.toCombMap.Dart),
    Nonempty (OEquivalentDiscDiagram X X') ∧
      (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
      P.inner.FollowsBoundary ∧ P.outer.FollowsBoundary ∧ C ∈ X'.relatorCells ∧
      C.face ∈ P.faces ∧ (cell X' i').face ∉ P.faces ∧ (cell X' j').face ∉ P.faces ∧
      invDarts X' P.outer.cycle = s₁ ++ invDarts X' A₁.darts ++ s₂ ++ invDarts X' A₂.darts ∧
      WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X' s₁)) ≤ eps ∧
      WordMetric.wordNorm D.alphabet.carrier (RelLetter.listVal (dartWord X' s₂)) ≤ eps

/-- **An exit of an O-equivalent copy is an exit** (Osin, proof of Lemma 9.7(b); `thm:hull`):
compose the two O-equivalences. -/
theorem TwoArcExit.of_oEquivalent {D : RelGenSet G Lambda} {eps : ℕ}
    {X X₁ : DiscDiagram.{u, w, v} W} (h : Nonempty (OEquivalentDiscDiagram X X₁))
    (hexit : TwoArcExit D eps X₁) : TwoArcExit D eps X := by
  obtain ⟨e₀⟩ := h
  obtain ⟨X', P, C, i', j', A₁, A₂, s₁, s₂, ⟨e⟩, hrest⟩ := hexit
  exact ⟨X', P, C, i', j', A₁, A₂, s₁, s₂, ⟨e₀.trans e⟩, hrest⟩

/-- **A pocket with two arcs outside is refuted below the bound** (Osin, proof of Lemma 9.7(b);
`thm:hull`).  The pocket region is a multiple-edge cut of `X` with fewer relator cells, and clause
(b) below the relator count of `X` gives Osin's degree contradiction. -/
theorem false_of_twoArcExit {D : RelGenSet G Lambda} {eps rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hlambda : 0 < lambda)
    (hlambda1 : lambda ≤ 1) (hc : 0 ≤ c) (hmu : 0 < mu) (hmu1 : mu ≤ 1 / 16) (hrho : 2 ≤ rho)
    (hlarge : lambda⁻¹ * (3 * (eps : ℝ) + c) < mu / 2 * (rho : ℝ))
    {X : DiscDiagram.{u, w, v} W} (hlea : X.LeastArea)
    (hbelow : OsinLemma97Below.{u, w, v} D lambda c mu eps W X.rCellCount)
    (hexit : TwoArcExit D eps X) : False := by
  obtain ⟨X', P, C, i', j', A₁, A₂, s₁, s₂, ⟨e⟩, hlabel', hin, hout, hC, hCf, hi, hj, hdec,
    hnorm₁, hnorm₂⟩ := hexit
  obtain ⟨cut⟩ := nonempty_osinMultipleEdgeCut_of_pocketRegion
    GeodesicCollar.StripStep.geodesicCollarStatement_holds pocketCellTransport hcondition hlambda1
    hc hlea e hlabel' P hin hout hC hCf hi hj A₁ A₂ s₁ s₂ hdec hnorm₁ hnorm₂
  have hrho0 : 0 < rho := by omega
  exact cut.false_of_below o52LeastArea hcondition hlambda hmu hmu1 hrho0 hlarge hlea
    (hbelow cut.enclosed cut.sections cut.leastArea cut.rCellCount_pos cut.rCellCount_lt)

end Exit

end GroupApproximation.Full.GL06g

#audit_axioms GroupApproximation.Full.GL06g.TwoArcExit.of_oEquivalent
#audit_axioms GroupApproximation.Full.GL06g.false_of_twoArcExit
