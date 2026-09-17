import GroupApproximation.Manuscript.NonMFNotes.Full.ExactResidual.Defects
import GroupApproximation.Sofic.SymmetricDoubleShulman
import GroupApproximation.Sofic.SymmetricDoubleMF
import GroupApproximation.Sofic.SymmetricDoubleCovering
import GroupApproximation.Sofic.CommensurabilityInvariance
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:exact-mf-residual`: what the residual identities are equivalent to

Manuscript `non_mf_group_notes.tex`, Section `sec:exact-residual`,
Theorem `thm:exact-mf-residual`:

> "`Res_MF(E) = D = N_conj`, `E/D ≅ Σ *_B (B × C₂)`, and `E/D` is MF.
> Moreover ... `Res_MF(E/⟨w⟩) = D_coll = D/⟨w⟩`,
> `Res_MF(E) = q⁻¹(D_coll)`."

`Full/ExactResidual/Defects.lean` proves the defect clauses
(`D = N_conj`, `E/D ≅ Σ *_B (B × C₂)`, `D ≤ Res_MF(E)`, `D/⟨w⟩ ≤ D_coll`).
This file proves that **every remaining clause is equivalent to the single
clause "`E/D` is MF"**, i.e. to `IsOperatorMF TerminalAmalgam`:

* `residual_eq_printedDefect_iff`: `Res_MF(E) = D ↔ E/D is MF`
  (the printed use of `cor:exactradical`);
* `terminalAmalgam_isOperatorMF_iff_exactResidual`: the three downstairs
  identities hold iff `Σ *_B (B × C₂)` is MF;
* `notesExactMFResidual_iff`: the whole printed theorem, bundled as
  `NotesExactMFResidual`, is equivalent to that one clause.

## The remaining gap, stated honestly

`IsOperatorMF TerminalAmalgam` is **not** proved in this repository. The printed
proof uses Shulman's symmetric amalgam theorem (arXiv:2603.13564, Theorem 10)
together with a conditional-expectation argument in the GNS von Neumann
algebra. A bespoke finite route is ruled out (`exactResidualObstruction`): in
every finite quotient of `Σ` the edge group `B` swallows the escape element,
so `Σ *_B (B × C₂)` is neither residually finite nor LEF, and any matrix model
has to be approximate in operator norm. The theorems here are therefore
equivalences. `NotesExactMFResidual` is a definition of the printed statement,
not a hypothesis of any theorem, and it is not claimed to hold.
-/

namespace GroupApproximation.Full.NN01

open LiteralNonMFPresentation LiteralSignFreeQuotient LiteralSignFreeRadicalReduction
open TerminalQuotientPresentation

noncomputable section

/-- **`E/D` is MF iff `Σ *_B (B × C₂)` is MF** (`thm:exact-mf-residual`,
`non_mf_group_notes.tex`), along `exactQuotientEquiv`. -/
theorem exactQuotient_isOperatorMF_iff :
    IsOperatorMF (MarkedGroup ⧸ printedDefect) ↔ IsOperatorMF TerminalAmalgam :=
  ⟨CommensurabilityInvariance.isOperatorMF_of_mulEquiv exactQuotientEquiv,
    CommensurabilityInvariance.isOperatorMF_of_mulEquiv exactQuotientEquiv.symm⟩

/-- **The three downstairs identities of `thm:exact-mf-residual` hold iff
`Σ *_B (B × C₂)` is MF** (`non_mf_group_notes.tex`). This composes the covering
equivalence `IsOperatorMF (Σ *_B (B × C₂)) ↔ IsOperatorMF (Σ *_B Σ)` with
`TerminalQuotientPresentation.manuscriptExactRadical_iff_symmetricDoubleMF`. -/
theorem terminalAmalgam_isOperatorMF_iff_exactResidual :
    IsOperatorMF TerminalAmalgam ↔
      (signFreeCollapseDefect = signFreePrintedDefect ∧
        actualCoronaMFResidual SignFreeQuotient = signFreePrintedDefect ∧
          actualCoronaMFResidual MarkedGroup =
            signFreeCollapseDefect.comap proj) :=
  (isOperatorMF_freeLampFlip_iff_isOperatorMF_symmetricDouble SigmaGroup sigmaBase).trans
    manuscriptExactRadical_iff_symmetricDoubleMF

/-- **`Res_MF(E) = D` iff `E/D` is MF** (`thm:exact-mf-residual` together with
`cor:exactradical`, `non_mf_group_notes.tex`). The forward direction also
recovers `Res_MF(E/⟨w⟩) = D/⟨w⟩ = D_coll`. -/
theorem residual_eq_printedDefect_iff :
    actualCoronaMFResidual MarkedGroup = printedDefect ↔ IsOperatorMF TerminalAmalgam := by
  constructor
  · intro hE
    have hc : (actualCoronaMFResidual SignFreeQuotient).comap proj =
        signFreePrintedDefect.comap proj := by
      rw [← actualCoronaMFResidual_markedGroup_eq_comap, hE,
        comap_proj_signFreePrintedDefect]
    have hSFQ : actualCoronaMFResidual SignFreeQuotient = signFreePrintedDefect :=
      Subgroup.comap_injective (QuotientGroup.mk'_surjective markSubgroup) hc
    have hcoll : signFreeCollapseDefect = signFreePrintedDefect :=
      le_antisymm (le_trans signFreeCollapseDefect_le_residual (le_of_eq hSFQ))
        signFreePrintedDefect_le_collapseDefect
    have hpull : actualCoronaMFResidual MarkedGroup = signFreeCollapseDefect.comap proj := by
      rw [hE, hcoll, comap_proj_signFreePrintedDefect]
    exact terminalAmalgam_isOperatorMF_iff_exactResidual.mpr ⟨hcoll, hSFQ, hpull⟩
  · intro hMF
    obtain ⟨hcoll, -, hpull⟩ := terminalAmalgam_isOperatorMF_iff_exactResidual.mp hMF
    rw [hpull, hcoll, comap_proj_signFreePrintedDefect]

/-- **`Res_MF(E) = N_conj` iff `E/D` is MF** (`thm:exact-mf-residual`,
`non_mf_group_notes.tex`). -/
theorem residual_eq_conjDefect_iff :
    actualCoronaMFResidual MarkedGroup = conjDefect ↔ IsOperatorMF TerminalAmalgam := by
  rw [conjDefect_eq_printedDefect]
  exact residual_eq_printedDefect_iff

/-- **The printed statement of `thm:exact-mf-residual`** (`non_mf_group_notes.tex`),
as a proposition:
`Res_MF(E) = D = N_conj`, `E/D ≅ Σ *_B (B × C₂)`, `E/D` MF,
`Res_MF(E/⟨w⟩) = D_coll = D/⟨w⟩`, and `Res_MF(E) = q⁻¹(D_coll)`.

This is a definition only. It is **not** proved: its MF clause is the open
analytic input described in the module docstring. -/
def NotesExactMFResidual : Prop :=
  signFreeCollapseDefect = signFreePrintedDefect ∧
    actualCoronaMFResidual SignFreeQuotient = signFreePrintedDefect ∧
      actualCoronaMFResidual MarkedGroup = signFreeCollapseDefect.comap proj ∧
        IsOperatorMF TerminalAmalgam ∧
          Nonempty (MarkedGroup ⧸ printedDefect ≃* TerminalAmalgam) ∧
            actualCoronaMFResidual MarkedGroup = printedDefect ∧
              printedDefect = conjDefect

/-- **The printed theorem is equivalent to its MF clause alone**
(`thm:exact-mf-residual`, `non_mf_group_notes.tex`). Every other clause is
proved unconditionally or follows from that clause. -/
theorem notesExactMFResidual_iff :
    NotesExactMFResidual ↔ IsOperatorMF TerminalAmalgam := by
  constructor
  · intro h
    unfold NotesExactMFResidual at h
    exact h.2.2.2.1
  · intro hMF
    obtain ⟨hcoll, hSFQ, hpull⟩ := terminalAmalgam_isOperatorMF_iff_exactResidual.mp hMF
    unfold NotesExactMFResidual
    exact ⟨hcoll, hSFQ, hpull, hMF, exactQuotient_nonempty_equiv,
      residual_eq_printedDefect_iff.mpr hMF, conjDefect_eq_printedDefect.symm⟩

/-- **Why the MF clause needs an approximate (norm) argument**
(`thm:exact-mf-residual`, `non_mf_group_notes.tex`). The edge group `B` is not
separable in `Σ`, so the terminal amalgam is neither residually finite nor LEF,
and the symmetric double `Σ *_B Σ` is not residually finite. No exact
finite-model argument reaches `IsOperatorMF TerminalAmalgam`. -/
theorem exactResidualObstruction :
    (∀ {Q : Type} [Group Q] [Finite Q] (φ : SigmaGroup →* Q),
        ∃ b ∈ sigmaBase, φ SymmetricDoubleMF.escapeElement = φ b) ∧
      SymmetricDoubleMF.escapeElement ∉ sigmaBase ∧
        ¬ Group.ResiduallyFinite TerminalAmalgam ∧
          ¬ IsLEF TerminalAmalgam ∧
            ¬ Group.ResiduallyFinite (SymmetricDouble SigmaGroup sigmaBase) :=
  ⟨fun φ ↦ SymmetricDoubleMF.sigmaBase_not_separable φ,
    SymmetricDoubleMF.escapeElement_not_mem_sigmaBase,
    SymmetricDoubleMF.terminalAmalgam_not_residuallyFinite,
    SymmetricDoubleMF.terminalAmalgam_not_isLEF,
    SymmetricDoubleMF.symmetricDouble_not_residuallyFinite⟩

/-- **Everything this lane proves about `thm:exact-mf-residual`**
(`non_mf_group_notes.tex`), in one proposition: the unconditional defect clauses,
the equivalence of the printed theorem with its MF clause, and the obstruction
to an exact finite-model proof of that clause. -/
theorem exactResidual_state :
    (quotHom.ker = printedDefect ∧
      Nonempty (MarkedGroup ⧸ printedDefect ≃* TerminalAmalgam) ∧
        conjDefect = printedDefect ∧
          printedDefect ≤ actualCoronaMFResidual MarkedGroup ∧
            signFreePrintedDefect ≤ signFreeCollapseDefect ∧
              signFreeCollapseDefect ≤ actualCoronaMFResidual SignFreeQuotient) ∧
      (NotesExactMFResidual ↔ IsOperatorMF TerminalAmalgam) ∧
        (actualCoronaMFResidual MarkedGroup = printedDefect ↔
          IsOperatorMF TerminalAmalgam) ∧
          ¬ Group.ResiduallyFinite TerminalAmalgam ∧ ¬ IsLEF TerminalAmalgam :=
  ⟨⟨quotHom_ker, exactQuotient_nonempty_equiv, conjDefect_eq_printedDefect,
      printedDefect_le_residual, signFreePrintedDefect_le_collapseDefect,
      signFreeCollapseDefect_le_residual⟩,
    notesExactMFResidual_iff, residual_eq_printedDefect_iff,
    exactResidualObstruction.2.2.1, exactResidualObstruction.2.2.2.1⟩

end

#audit_closed_axioms GroupApproximation.Full.NN01.exactQuotient_isOperatorMF_iff
#audit_closed_axioms GroupApproximation.Full.NN01.terminalAmalgam_isOperatorMF_iff_exactResidual
#audit_closed_axioms GroupApproximation.Full.NN01.residual_eq_printedDefect_iff
#audit_closed_axioms GroupApproximation.Full.NN01.residual_eq_conjDefect_iff
#audit_closed_axioms GroupApproximation.Full.NN01.notesExactMFResidual_iff
#audit_closed_axioms GroupApproximation.Full.NN01.exactResidualObstruction
#audit_closed_axioms GroupApproximation.Full.NN01.exactResidual_state

end GroupApproximation.Full.NN01
