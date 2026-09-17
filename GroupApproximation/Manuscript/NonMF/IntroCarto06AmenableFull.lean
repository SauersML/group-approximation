import GroupApproximation.Manuscript.OneSidedMFRadical.AffineCliffordTrace
import GroupApproximation.Manuscript.OneSidedMFRadical.AmenableTraceTheorem
import GroupApproximation.Sofic.CommutingLampCollapse
import GroupApproximation.Sofic.LiteralWitnessConsequences
import GroupApproximation.Sofic.CommensurabilityInvariance
import GroupApproximation.Manuscript.NonMF.IntroAmenable.LiteralMF
import GroupApproximation.Manuscript.NonMF.IntroAmenable.KorchaginDirectLimit
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:amenable-trace`, the whole printed paragraph as one theorem (lane nm-intro-06)

`non_mf_groups_exist.tex`, lines 261–292:

> There is a sofic group $W=W_0\rtimes\mathbb Z$, with $W_0$ locally residually
> finite, that is not MF\@.  The canonical trace on $C^*_{\max}(W_0)$ is
> quasidiagonal, and the canonical trace on $C^*_{\max}(W)$ is amenable
> and not quasidiagonal.  (tex 263–266)

> Since $W_0$ is a direct limit of residually finite groups, it is MF
> [Korchagin, Corollary 10 and Proposition 13].  So MF groups are not closed under
> semidirect products with $\mathbb Z$ ...  (tex 284–287)

MF is printed for countable groups (tex 87), so both `W` and `W₀` are displayed countable, and
"MF" is stated both for the Introduction's literal definition `IntroAmenable.LiteralMF` and for
the corpus predicate `IsOperatorMF` (they agree on countable groups,
`IntroAmenable.literalMF_iff_isOperatorMF`).

## Proof route (pure assembly, nothing assumed)

The witnesses are `LiteralNonMFLinearWitness.WitnessGroup`,
`CliffordWitnessLocallyRFByInt.ShiftKernel` and `CliffordWitnessLocallyRFByInt.shiftAction`.

* Reassociation, local residual finiteness of `W₀`, soficity of `W`, `¬ IsOperatorMF W`, the
  quasidiagonal canonical trace of `W₀`, and the amenable non-quasidiagonal canonical trace of `W`:
  `AmenableTraceTheorem.manuscriptAffineCliffordConclusions` (closed; the `W₀` trace clause is the
  same input `AmenableExtensionTrace.manuscriptPrintedLocallyRFCanonicalTraceQuasidiagonal` used by
  `printedAmenableNonquasidiagonalTraceCountable`, taken here at the concrete kernel instead of
  through the existential).
* `W₀` is an injective direct limit of residually finite groups and is MF:
  `IntroAmenable.manuscriptSentence_shiftKernelDirectLimitMF` (Korchagin Cor. 10 and Prop. 13,
  proved in `KorchaginDirectLimit.lean`).
* MF is not closed under `⋊ ℤ`: transport `¬ IsOperatorMF WitnessGroup` along
  `witnessGroupEquivShiftKernelByInt`; countability of `W₀ ⋊ ℤ` is the image of the countable
  `WitnessGroup` under that equivalence.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroCarto06

/-- **tex 263–286, `thm:amenable-trace` with the remark after it, as one theorem.**  There are
countable groups `W ≅ W₀ ⋊ ℤ` with `W₀` locally residually finite and an injective direct limit of
residually finite groups (hence MF), `W` sofic and not MF, the canonical trace on `C*_max(W₀)`
quasidiagonal, and the canonical trace on `C*_max(W)` amenable and not quasidiagonal. -/
theorem manuscriptSentence_amenableTraceTheoremFull :
    ∃ (W W₀ : Type) (_ : Group W) (_ : Group W₀) (_ : Countable W) (_ : Countable W₀)
      (φ : Multiplicative ℤ →* MulAut W₀),
      Nonempty (W ≃* (W₀ ⋊[φ] Multiplicative ℤ)) ∧
        GroupApproximation.LocallyRFByIntAmenableTrace.IsLocallyResiduallyFinite W₀ ∧
        GroupApproximation.Manuscript.NonMF.IntroAmenable.IsInjectiveDirectLimitOfResiduallyFinite
          W₀ ∧
        GroupApproximation.Manuscript.NonMF.IntroAmenable.LiteralMF W₀ ∧
        GroupApproximation.IsOperatorMF W₀ ∧
        GroupApproximation.IsSofic W ∧
        ¬ GroupApproximation.Manuscript.NonMF.IntroAmenable.LiteralMF W ∧
        ¬ GroupApproximation.IsOperatorMF W ∧
        GroupApproximation.Quasidiagonal.IsQuasidiagonalTrace
          (fun a : GroupApproximation.MaximalGroupCStar W₀ ↦
            GroupApproximation.canonicalMaximalTrace W₀ a) ∧
        GroupApproximation.Quasidiagonal.IsAmenableTrace
          (fun a : GroupApproximation.MaximalGroupCStar W ↦
            GroupApproximation.canonicalMaximalTrace W a) ∧
        ¬ GroupApproximation.Quasidiagonal.IsQuasidiagonalTrace
          (fun a : GroupApproximation.MaximalGroupCStar W ↦
            GroupApproximation.canonicalMaximalTrace W a) := by
  obtain ⟨hEquiv, hLRF, hSofic, hNotMF, hW₀QD, hAmen, hNotQD⟩ :=
    GroupApproximation.AmenableTraceTheorem.manuscriptAffineCliffordConclusions
  obtain ⟨hLim, hLit₀, hMF₀⟩ :=
    GroupApproximation.Manuscript.NonMF.IntroAmenable.manuscriptSentence_shiftKernelDirectLimitMF
  exact ⟨GroupApproximation.LiteralNonMFLinearWitness.WitnessGroup,
    GroupApproximation.CliffordWitnessLocallyRFByInt.ShiftKernel, inferInstance, inferInstance,
    inferInstance, inferInstance, GroupApproximation.CliffordWitnessLocallyRFByInt.shiftAction,
    hEquiv, hLRF, hLim, hLit₀, hMF₀, hSofic,
    fun hL => hNotMF
      ((GroupApproximation.Manuscript.NonMF.IntroAmenable.literalMF_iff_isOperatorMF
        GroupApproximation.LiteralNonMFLinearWitness.WitnessGroup).mp hL),
    hNotMF, hW₀QD, hAmen, hNotQD⟩

/-- **tex 286–287.**  "MF groups are not closed under semidirect products with `ℤ`": there is a
countable MF group `K` and an action `φ` of `ℤ` such that the countable group `K ⋊[φ] ℤ` is not
MF, in the literal sense and as `IsOperatorMF`. -/
theorem manuscriptSentence_mfNotClosedUnderIntSemidirect :
    ∃ (K : Type) (_ : Group K) (_ : Countable K) (φ : Multiplicative ℤ →* MulAut K),
      Countable (K ⋊[φ] Multiplicative ℤ) ∧
        GroupApproximation.Manuscript.NonMF.IntroAmenable.LiteralMF K ∧
        GroupApproximation.IsOperatorMF K ∧
        ¬ GroupApproximation.Manuscript.NonMF.IntroAmenable.LiteralMF
          (K ⋊[φ] Multiplicative ℤ) ∧
        ¬ GroupApproximation.IsOperatorMF (K ⋊[φ] Multiplicative ℤ) := by
  obtain ⟨-, hLit₀, hMF₀⟩ :=
    GroupApproximation.Manuscript.NonMF.IntroAmenable.manuscriptSentence_shiftKernelDirectLimitMF
  have hNotMF : ¬ GroupApproximation.IsOperatorMF
      (GroupApproximation.CliffordWitnessLocallyRFByInt.ShiftKernel ⋊[
        GroupApproximation.CliffordWitnessLocallyRFByInt.shiftAction] Multiplicative ℤ) :=
    fun hMF => GroupApproximation.LiteralWitnessConsequences.witnessGroup_not_isOperatorMF
      (GroupApproximation.CommensurabilityInvariance.isOperatorMF_of_mulEquiv
        GroupApproximation.CliffordWitnessLocallyRFByInt.witnessGroupEquivShiftKernelByInt.symm hMF)
  have hCount : Countable
      (GroupApproximation.CliffordWitnessLocallyRFByInt.ShiftKernel ⋊[
        GroupApproximation.CliffordWitnessLocallyRFByInt.shiftAction] Multiplicative ℤ) :=
    GroupApproximation.CliffordWitnessLocallyRFByInt.witnessGroupEquivShiftKernelByInt.surjective.countable
  exact ⟨GroupApproximation.CliffordWitnessLocallyRFByInt.ShiftKernel, inferInstance,
    inferInstance, GroupApproximation.CliffordWitnessLocallyRFByInt.shiftAction, hCount,
    hLit₀, hMF₀,
    fun hL => hNotMF
      ((GroupApproximation.Manuscript.NonMF.IntroAmenable.literalMF_iff_isOperatorMF
        (GroupApproximation.CliffordWitnessLocallyRFByInt.ShiftKernel ⋊[
          GroupApproximation.CliffordWitnessLocallyRFByInt.shiftAction] Multiplicative ℤ)).mp hL),
    hNotMF⟩

end IntroCarto06
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto06.manuscriptSentence_amenableTraceTheoremFull
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroCarto06.manuscriptSentence_mfNotClosedUnderIntSemidirect
