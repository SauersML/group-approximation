import GroupApproximation.Sofic.TerminalQuotientIso
import GroupApproximation.Sofic.LiteralSignFreeRadicalReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:exact-mf-residual`: the defect side, unconditionally

Manuscript `non_mf_group_notes.tex`, Section `sec:exact-residual`,
Theorem `thm:exact-mf-residual`:

> "For the group `E` of Definition `def:E`, put `d = ĉ = tct⁻¹`, `u = [d,v₁]`,
> and `D = ⟨⟨u⟩⟩_E`.  Then `Res_MF(E) = D = N_conj`,
> `E/D ≅ Σ *_B (B × C₂)`, and `E/D` is MF."

This file proves every clause of that theorem which does not pass through
operator MF of `Σ *_B (B × C₂)`:

* `quotHom_ker`: the kernel of `E ↠ (E/⟨w⟩)/(D/⟨w⟩)` is exactly `D`, so the
  repository's terminal quotient *is* `E/D`;
* `exactQuotientEquiv`: `E/D ≃* Σ *_B (B × C₂)` (the printed presentation
  calculation, `TerminalQuotientPresentation.terminalEquiv`, transported to
  `E/D` itself);
* `conjDefect_eq_printedDefect`: `D = N_conj`, with
  `N_conj = ⟨⟨[ĉ, ι(λ)] : λ ∈ B⟩⟩` (Definition `def:pattern`);
* `signFreePrintedDefect_eq_map`: `D/⟨w⟩` is the image of `D`;
* the elementary half of the residual identities: `D ≤ Res_MF(E)`,
  `D/⟨w⟩ ≤ D_coll ≤ Res_MF(E/⟨w⟩)` (the proof's
  "`D ≤ Res_MF(E)`" and "`D/⟨w⟩ ≤ D_coll`").

The proof of `D = N_conj` differs from the printed seven-word calculation:
the inclusion `N_conj ≤ D` is read off the terminal quotient, where
`TerminalQuotientPresentation.quotHom_commute_baseMap` already shows that the
moved lamp centralizes the whole base modulo `D`.
-/

namespace GroupApproximation.Full.NN01

open LiteralNonMFPresentation LiteralSignFreeQuotient LiteralSignFreeRadicalReduction
open TerminalQuotientPresentation
open scoped commutatorElement

noncomputable section

/-! ## `D/⟨w⟩` is the image of `D` -/

/-- **`D/⟨w⟩ = q(D)`** (`thm:exact-mf-residual`, `non_mf_group_notes.tex`):
the printed defect downstairs, the normal closure of `⁅v₁, d⁆` in `E/⟨w⟩`, is
the image of the printed defect `D = ⟨⟨u⟩⟩_E` under `q : E ↠ E/⟨w⟩`. -/
theorem signFreePrintedDefect_eq_map :
    signFreePrintedDefect = printedDefect.map proj := by
  apply le_antisymm
  · haveI : (printedDefect.map proj).Normal :=
      Subgroup.Normal.map printedDefect_normal proj
        (QuotientGroup.mk'_surjective markSubgroup)
    apply Subgroup.normalClosure_le_normal
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    show ⁅proj (baseMap baseV1), proj dee⁆ ∈ printedDefect.map proj
    rw [← map_commutatorElement proj (baseMap baseV1) dee,
      ← commutatorElement_inv dee (baseMap baseV1)]
    exact Subgroup.mem_map_of_mem proj
      (Subgroup.inv_mem _ unsquaredDefect_mem_printedDefect)
  · exact Subgroup.map_le_iff_le_comap.mpr
      printedDefect_le_comap_signFreePrintedDefect

/-- **`q⁻¹(D/⟨w⟩) = D`** (`thm:exact-mf-residual`, `non_mf_group_notes.tex`):
since `⟨w⟩ ≤ D` (`w = u²`), pulling the downstairs defect back loses nothing. -/
theorem comap_proj_signFreePrintedDefect :
    signFreePrintedDefect.comap proj = printedDefect := by
  apply le_antisymm
  · intro x hx
    have hx' : proj x ∈ printedDefect.map proj := by
      rw [← signFreePrintedDefect_eq_map]
      exact hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
    obtain ⟨z, hz, hyz⟩ := (QuotientGroup.mk'_eq_mk' markSubgroup).mp hyx
    rw [← hyz]
    exact Subgroup.mul_mem _ hy (markSubgroup_le_printedDefect hz)
  · exact printedDefect_le_comap_signFreePrintedDefect

/-! ## The terminal quotient is `E/D` -/

/-- **`ker (E ↠ (E/⟨w⟩)/(D/⟨w⟩)) = D`** (`thm:exact-mf-residual`,
`non_mf_group_notes.tex`). -/
theorem quotHom_ker : quotHom.ker = printedDefect := by
  rw [← comap_proj_signFreePrintedDefect]
  ext x
  rw [MonoidHom.mem_ker, quotHom_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_comap]

/-- **`E/D ≅ Σ *_B (B × C₂)`** (`thm:exact-mf-residual`,
`non_mf_group_notes.tex`): the printed presentation calculation, at the
quotient of `E` by `D = ⟨⟨u⟩⟩_E` itself. -/
def exactQuotientEquiv : MarkedGroup ⧸ printedDefect ≃* TerminalAmalgam :=
  (QuotientGroup.quotientMulEquivOfEq quotHom_ker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective quotHom quotHom_surjective).trans
      terminalEquiv)

/-- The isomorphism `E/D ≃* Σ *_B (B × C₂)` exists
(`thm:exact-mf-residual`, `non_mf_group_notes.tex`). -/
theorem exactQuotient_nonempty_equiv :
    Nonempty (MarkedGroup ⧸ printedDefect ≃* TerminalAmalgam) :=
  ⟨exactQuotientEquiv⟩

/-! ## `D = N_conj` -/

/-- The normal closure `N_conj = ⟨⟨[ĉ, ι(λ)] : λ ∈ B⟩⟩_E` of the Kazhdan
conjugation datum of `E` (Definition `def:pattern`, `non_mf_group_notes.tex`),
with `ĉ = d = tct⁻¹` the moved lamp and `ι = baseMap`. -/
def conjDefect : Subgroup MarkedGroup :=
  Subgroup.normalClosure {g : MarkedGroup | ∃ b : Base, g = ⁅dee, baseMap b⁆}

instance conjDefect_normal : conjDefect.Normal :=
  Subgroup.normalClosure_normal

/-- **Every commutator `[ĉ, ι(b)]` lies in `D`** (`thm:exact-mf-residual`,
`non_mf_group_notes.tex`: "every nontrivial `[d,b]` is a conjugate of `u`"). -/
theorem commutator_dee_baseMap_mem_printedDefect (b : Base) :
    ⁅dee, baseMap b⁆ ∈ printedDefect := by
  rw [← quotHom_ker, MonoidHom.mem_ker, map_commutatorElement quotHom dee (baseMap b)]
  exact commutatorElement_eq_one_iff_commute.mpr (quotHom_commute_baseMap b).symm

/-- **`D = N_conj`** (`thm:exact-mf-residual`, `non_mf_group_notes.tex`). -/
theorem conjDefect_eq_printedDefect : conjDefect = printedDefect := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro g hg
    rw [Set.mem_setOf_eq] at hg
    obtain ⟨b, rfl⟩ := hg
    exact commutator_dee_baseMap_mem_printedDefect b
  · apply Subgroup.normalClosure_mono
    rw [Set.singleton_subset_iff, Set.mem_setOf_eq]
    exact ⟨baseV1, rfl⟩

/-! ## The elementary half of the residual identities -/

/-- **`D_coll ≤ Res_MF(E/⟨w⟩)`** (`thm:exact-mf-residual`, via
`cor:pullback`, `non_mf_group_notes.tex`): the collapse defect is contained in
the MF residual of the sign-free quotient. -/
theorem signFreeCollapseDefect_le_residual :
    signFreeCollapseDefect ≤ actualCoronaMFResidual SignFreeQuotient := by
  intro x hx
  have hq : QuotientGroup.mk' signFreeCollapseDefect x = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hx
  rw [manuscriptSignFreeRadicalReduction.1, Subgroup.mem_comap, hq]
  exact Subgroup.one_mem _

/-- **`D/⟨w⟩ ≤ Res_MF(E/⟨w⟩)`** (`thm:exact-mf-residual`,
`non_mf_group_notes.tex`). -/
theorem signFreePrintedDefect_le_residual :
    signFreePrintedDefect ≤ actualCoronaMFResidual SignFreeQuotient :=
  le_trans signFreePrintedDefect_le_collapseDefect signFreeCollapseDefect_le_residual

/-- **`D ≤ Res_MF(E)`** (`thm:exact-mf-residual`, `non_mf_group_notes.tex`:
"`u ∈ Res_MF(E)` by Theorem `thm:signfree`; since the residual is normal,
`D ≤ Res_MF(E)`"). -/
theorem printedDefect_le_residual :
    printedDefect ≤ actualCoronaMFResidual MarkedGroup := by
  rw [actualCoronaMFResidual_markedGroup_eq_comap, ← comap_proj_signFreePrintedDefect]
  exact Subgroup.comap_mono signFreePrintedDefect_le_residual

/-- **`N_conj ≤ Res_MF(E)`** (`thm:exact-mf-residual`,
`non_mf_group_notes.tex`). -/
theorem conjDefect_le_residual :
    conjDefect ≤ actualCoronaMFResidual MarkedGroup := by
  rw [conjDefect_eq_printedDefect]
  exact printedDefect_le_residual

/-- **The unconditional defect clauses of `thm:exact-mf-residual`**
(`non_mf_group_notes.tex`), bundled: `ker(E ↠ T) = D`, `E/D ≅ Σ *_B (B × C₂)`,
`D = N_conj`, `⟨w⟩ ≤ D`, `D/⟨w⟩ = q(D)`, `q⁻¹(D/⟨w⟩) = D`,
`D/⟨w⟩ ≤ D_coll ≤ Res_MF(E/⟨w⟩)` and `D ≤ Res_MF(E)`. -/
theorem exactResidualDefects :
    quotHom.ker = printedDefect ∧
      Nonempty (MarkedGroup ⧸ printedDefect ≃* TerminalAmalgam) ∧
        conjDefect = printedDefect ∧
          markSubgroup ≤ printedDefect ∧
            signFreePrintedDefect = printedDefect.map proj ∧
              signFreePrintedDefect.comap proj = printedDefect ∧
                signFreePrintedDefect ≤ signFreeCollapseDefect ∧
                  signFreeCollapseDefect ≤ actualCoronaMFResidual SignFreeQuotient ∧
                    printedDefect ≤ actualCoronaMFResidual MarkedGroup :=
  ⟨quotHom_ker, exactQuotient_nonempty_equiv, conjDefect_eq_printedDefect,
    markSubgroup_le_printedDefect, signFreePrintedDefect_eq_map,
    comap_proj_signFreePrintedDefect, signFreePrintedDefect_le_collapseDefect,
    signFreeCollapseDefect_le_residual, printedDefect_le_residual⟩

end

#audit_closed_axioms GroupApproximation.Full.NN01.signFreePrintedDefect_eq_map
#audit_closed_axioms GroupApproximation.Full.NN01.comap_proj_signFreePrintedDefect
#audit_closed_axioms GroupApproximation.Full.NN01.quotHom_ker
#audit_closed_axioms GroupApproximation.Full.NN01.exactQuotientEquiv
#audit_closed_axioms GroupApproximation.Full.NN01.conjDefect_eq_printedDefect
#audit_closed_axioms GroupApproximation.Full.NN01.signFreeCollapseDefect_le_residual
#audit_closed_axioms GroupApproximation.Full.NN01.printedDefect_le_residual
#audit_closed_axioms GroupApproximation.Full.NN01.conjDefect_le_residual
#audit_closed_axioms GroupApproximation.Full.NN01.exactResidualDefects

end GroupApproximation.Full.NN01
