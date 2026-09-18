import GroupApproximation.Manuscript.NonMF.Full.GL06h3.Statement
import GroupApproximation.Manuscript.NonMF.Full.GL06h1.SubdiagramLabels
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixDescentCut
import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.Meta.AxiomGuard

/-!
# GL06h3: the all-cells short enclosed face set from a short boundary

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

Let `X` be a least-area diagram with a relator cell and letter labels, and let an enclosed face
set hold every relator cell of `X`, with an outer walk of length at most `ε + ε`.  The enclosed
subdiagram `Ξ` (`GL06h1.closedWalkEnclosedSubdiagramSucc_labels`) has least area, a relator cell,
at most as many relator cells as `X`, letter labels, and boundary word the inverse outer walk, of
length at most `ε + ε`.  Clause (b) below the count of `X` restricts to clause (b) below the count
of `Ξ`.  A refutation of short boundaries refutes `Ξ`.

* `allCellsShortEnclosedRefutedBelowInput_of_shortBoundary`: at fixed parameters.
* `allCellsShortEnclosedRefutedBelowSection_of_shortBoundarySection`: beyond thresholds.

## Manuscript status

Infrastructure for `thm:hull` (non_mf_groups_exist.tex ~2121); certifies no printed sentence on
its own.
-/

namespace GroupApproximation.Full.GL06h3

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **An all-cells short enclosed face set gives a short boundary** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121).  At fixed parameters, the refutation of short
boundaries below the inductive bound refutes the all-cells short enclosed face set. -/
theorem allCellsShortEnclosedRefutedBelowInput_of_shortBoundary {D : RelGenSet G Lambda}
    {lambda c mu : ℝ} {eps : ℕ} {W : Set (List (RelLetter G Lambda))}
    (hshort : ShortBoundaryRefutedBelowInput.{u, w, v} D lambda c mu eps W) :
    GL06e.AllCellsShortEnclosedRefutedBelowInput.{u, w, v} D lambda c mu eps W := by
  intro X hlea hbelow hletters hW hpos faces outerWalk hE hall hlen
  obtain ⟨Xi, hword, hposXi, hcount, hleaXi, hlabel⟩ :=
    GL06h1.closedWalkEnclosedSubdiagramSucc_labels X faces outerWalk hE
  have hcell : ∃ C ∈ X.relatorCells, C.face ∈ faces :=
    ⟨Embedded.cell X ⟨0, hpos⟩, Embedded.cell_mem X ⟨0, hpos⟩,
      hall _ (Embedded.cell_mem X ⟨0, hpos⟩)⟩
  have hlettersXi : ∀ d, (symmetricLabelAlphabet D).IsLetter (Xi.label d) := by
    intro d
    obtain ⟨d', hd'⟩ := hlabel d
    rw [hd']
    exact hletters d'
  have hlenXi : Xi.boundaryWord.length ≤ eps + eps := by
    rw [hword]
    simp only [Embedded.dartWord, Embedded.invDarts, List.length_map, List.length_reverse]
    exact hlen
  exact hshort Xi (hleaXi hlea) (hbelow.mono hcount) hlettersXi hW (hposXi hcell) hlenXi

end Input

/-- **An all-cells short enclosed face set gives a short boundary, beyond thresholds** (Osin, proof
of Lemma 9.7(b); `thm:hull`, non_mf_groups_exist.tex ~2121).  The thresholds of the short-boundary
refutation serve unchanged. -/
theorem allCellsShortEnclosedRefutedBelowSection_of_shortBoundarySection
    (hshort : ShortBoundaryRefutedBelowSectionStatement.{u, w, v}) :
    GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement.{u, w, v} := by
  intro _G _ _Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  obtain ⟨eps0, heps0⟩ := hshort D hhyp lambda c mu hlambda hlambda1 hc hmu hmu1
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hcondition =>
    allCellsShortEnclosedRefutedBelowInput_of_shortBoundary (hrho rho hrho' W hcondition)⟩

end GroupApproximation.Full.GL06h3

#audit_axioms GroupApproximation.Full.GL06h3.allCellsShortEnclosedRefutedBelowInput_of_shortBoundary
#audit_axioms GroupApproximation.Full.GL06h3.allCellsShortEnclosedRefutedBelowSection_of_shortBoundarySection
