import GroupApproximation.Manuscript.NonMFSentences.KorchaginDirectLimit
import GroupApproximation.Sofic.CliffordWitnessLocallyRFByInt
import GroupApproximation.Sofic.LiteralWitnessConsequences
import GroupApproximation.Sofic.CommensurabilityInvariance
import GroupApproximation.Meta.AxiomGuard

/-!
# `W_0` is MF as a direct limit, and Korchagin's semidirect question

`non_mf_groups_exist.tex`, after `thm:amenable-trace` (origin/main, lines 272-276):

> Since `W_0` is a direct limit of residually finite groups, it is
> MF~\cite[Corollary~10 and Proposition~13]{Korchagin}.  So MF groups are not
> closed under semidirect products with `ℤ`, which answers a question of
> Korchagin~\cite[remark following Proposition~12]{Korchagin}.

`AmenableTraceTheorem.manuscriptShiftKernelIsOperatorMF` proves `W_0` MF by a
different route (locally residually finite ⇒ LEF ⇒ MF).  This module follows
the printed route instead.  `W_0 = Cl(X) ⋊ T_α` (tex line 1525) is the shift
kernel `CliffordWitnessLocallyRFByInt.ShiftKernel`.  By tex lines 1562-1566, its
finitely generated subgroups are residually finite and `W_0` is their directed
union.  So `W_0` is a direct limit of residually finite groups, each MF by
Korchagin's Corollary 10, and `W_0` is MF by Proposition 13
(`KorchaginDirectLimit`).

Korchagin's remark after Proposition 12 (arXiv:1704.06906, §2): "Remark that we
can prove only this weak permanent fact about cross product.  We do not know
answer also in the case of `K = ℤ`".  The question is whether `G ⋊ ℤ` is MF for
every MF group `G`.  It is stated as `KorchaginSemidirectIntQuestion`, and
refuted by `W = W_0 ⋊ ℤ`, which is not MF.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace KorchaginShiftKernelMF

open CliffordWitnessLocallyRFByInt LocallyRFByIntAmenableTrace KorchaginDirectLimit

/-- **Printed** (tex lines 272-274): "Since `W_0` is a direct limit of
residually finite groups, it is MF~\cite[Corollary~10 and
Proposition~13]{Korchagin}."  The first conjunct is the direct-limit
presentation: a directed family of residually finite subgroups covering `W_0`.
The second is the conclusion. -/
def PrintedShiftKernelDirectLimitMF : Prop :=
  (∃ (ι : Type) (H : ι → Subgroup ShiftKernel),
      Directed (· ≤ ·) H ∧ (∀ g : ShiftKernel, ∃ i, g ∈ H i) ∧
        ∀ i, Group.ResiduallyFinite (H i)) ∧
    IsOperatorMF ShiftKernel

/-- The finitely generated subgroups of `W_0` present it as a direct limit of
residually finite groups (tex lines 1562-1566). -/
theorem shiftKernel_directLimit_residuallyFinite :
    ∃ (ι : Type) (H : ι → Subgroup ShiftKernel),
      Directed (· ≤ ·) H ∧ (∀ g : ShiftKernel, ∃ i, g ∈ H i) ∧
        ∀ i, Group.ResiduallyFinite (H i) :=
  ⟨{H : Subgroup ShiftKernel // H.FG}, fun H ↦ H.1, directed_fgSubgroups ShiftKernel,
    exists_fgSubgroup_mem, fun H ↦ shiftKernel_isLocallyResiduallyFinite H.1 H.2⟩

/-- Closed proof along the printed route: each member is MF by Corollary 10,
and the union is MF by Proposition 13. -/
theorem manuscriptShiftKernelDirectLimitMF : PrintedShiftKernelDirectLimitMF := by
  refine ⟨shiftKernel_directLimit_residuallyFinite, ?_⟩
  obtain ⟨ι, H, hdir, hcover, hRF⟩ := shiftKernel_directLimit_residuallyFinite
  exact korchaginPropositionThirteenForUnions ShiftKernel ι H hdir hcover fun i ↦ by
    haveI := hRF i
    exact isOperatorMF_of_residuallyFinite_viaCorollaryTen

/-- **Printed** (tex lines 274-275): "So MF groups are not closed under
semidirect products with `ℤ`."  The MF half is the printed-route
`manuscriptShiftKernelDirectLimitMF`. -/
def PrintedMFNotClosedUnderIntSemidirect : Prop :=
  ∃ (K : Type) (_ : Group K) (_ : Countable K) (φ : Multiplicative ℤ →* MulAut K),
    IsOperatorMF K ∧ ¬ IsOperatorMF (K ⋊[φ] Multiplicative ℤ)

theorem manuscriptMFNotClosedUnderIntSemidirectPrintedRoute :
    PrintedMFNotClosedUnderIntSemidirect := by
  refine ⟨ShiftKernel, inferInstance, inferInstance, shiftAction,
    manuscriptShiftKernelDirectLimitMF.2, ?_⟩
  intro hMF
  exact LiteralWitnessConsequences.witnessGroup_not_isOperatorMF
    (CommensurabilityInvariance.isOperatorMF_of_mulEquiv
      witnessGroupEquivShiftKernelByInt.symm hMF)

/-- Korchagin's question (remark following Proposition 12): is `G ⋊ ℤ` MF for
every MF group `G`?  Korchagin considers only countable groups. -/
def KorchaginSemidirectIntQuestion : Prop :=
  ∀ (K : Type) [Group K] [Countable K] (φ : Multiplicative ℤ →* MulAut K),
    IsOperatorMF K → IsOperatorMF (K ⋊[φ] Multiplicative ℤ)

/-- **Printed** (tex lines 275-276): "…which answers a question of
Korchagin~\cite[remark following Proposition~12]{Korchagin}": the answer is
negative. -/
def PrintedAnswersKorchaginQuestion : Prop :=
  ¬ KorchaginSemidirectIntQuestion

theorem manuscriptAnswersKorchaginQuestion : PrintedAnswersKorchaginQuestion := by
  intro hQ
  obtain ⟨K, _, _, φ, hK, hnot⟩ := manuscriptMFNotClosedUnderIntSemidirectPrintedRoute
  exact hnot (hQ K φ hK)

end KorchaginShiftKernelMF
end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMFSentences.KorchaginShiftKernelMF

#audit_closed_axioms shiftKernel_directLimit_residuallyFinite
#audit_closed_axioms manuscriptShiftKernelDirectLimitMF
#audit_closed_axioms manuscriptMFNotClosedUnderIntSemidirectPrintedRoute
#audit_closed_axioms manuscriptAnswersKorchaginQuestion
