import GroupApproximation.Manuscript.OneSidedMFRadical.AmenableTraceTheorem
import GroupApproximation.Sofic.CommutingLampCollapse
import GroupApproximation.Manuscript.NonMF.IntroAmenable.LiteralMF
import GroupApproximation.Meta.AxiomGuard

/-!
# A sofic group that is not MF (`thm:amenable-trace`, first sentence; abstract, first half)

`non_mf_groups_exist.tex`, line 263:

> There is a sofic group $W=W_0\rtimes\mathbb Z$, with $W_0$ locally residually
> finite, that is not MF\@.

`non_mf_groups_exist.tex`, line 66 (abstract), first half:

> We also construct a sofic group that is not MF, whose canonical trace on the maximal group
> $C^*$-algebra is amenable but not quasidiagonal, ...

## Proof route

Both endpoints are existential statements whose witness is the concrete affine--Clifford
witness `LiteralNonMFLinearWitness.WitnessGroup` with kernel
`CliffordWitnessLocallyRFByInt.ShiftKernel`.  All conclusions come from the closed theorem
`AmenableTraceTheorem.manuscriptAmenableNonquasidiagonalTraceCore` (reassociation equivalence,
local residual finiteness of the kernel, soficity, failure of operator-MF, amenability and
non-quasidiagonality of the canonical maximal trace).  "Not MF" is stated both for the
Introduction's printed definition `LiteralMF` and for the corpus predicate `IsOperatorMF`,
using `literalMF_iff_isOperatorMF`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace IntroAmenable

/-- **tex 263.**  There is a sofic group `W = W₀ ⋊ ℤ`, with `W₀` locally residually finite,
that is not MF. -/
theorem manuscriptSentence_soficNonMFSemidirect :
    ∃ (W W₀ : Type) (_ : Group W) (_ : Group W₀) (_ : Countable W) (_ : Countable W₀)
      (φ : Multiplicative ℤ →* MulAut W₀),
      Nonempty (W ≃* (W₀ ⋊[φ] Multiplicative ℤ)) ∧
        GroupApproximation.LocallyRFByIntAmenableTrace.IsLocallyResiduallyFinite W₀ ∧
        GroupApproximation.IsSofic W ∧ ¬ LiteralMF W ∧ ¬ GroupApproximation.IsOperatorMF W := by
  obtain ⟨he, hLRF, hSofic, hNotMF, -, -⟩ :=
    GroupApproximation.AmenableTraceTheorem.manuscriptAmenableNonquasidiagonalTraceCore
  exact ⟨GroupApproximation.LiteralNonMFLinearWitness.WitnessGroup,
    GroupApproximation.CliffordWitnessLocallyRFByInt.ShiftKernel, inferInstance, inferInstance,
    inferInstance, inferInstance, GroupApproximation.CliffordWitnessLocallyRFByInt.shiftAction,
    he, hLRF, hSofic, fun hL => hNotMF
      ((literalMF_iff_isOperatorMF GroupApproximation.LiteralNonMFLinearWitness.WitnessGroup).mp hL), hNotMF⟩

/-- **tex 66, first half.**  There is a sofic group that is not MF, whose canonical trace on the
maximal group `C*`-algebra is amenable but not quasidiagonal. -/
theorem manuscriptSentence_soficNonMFAmenableNonQDTrace :
    ∃ (W : Type) (_ : Group W) (_ : Countable W),
      GroupApproximation.IsSofic W ∧ ¬ LiteralMF W ∧ ¬ GroupApproximation.IsOperatorMF W ∧
        GroupApproximation.Quasidiagonal.IsAmenableTrace
          (fun a : GroupApproximation.MaximalGroupCStar W ↦
            GroupApproximation.canonicalMaximalTrace W a) ∧
        ¬ GroupApproximation.Quasidiagonal.IsQuasidiagonalTrace
          (fun a : GroupApproximation.MaximalGroupCStar W ↦
            GroupApproximation.canonicalMaximalTrace W a) := by
  obtain ⟨-, -, hSofic, hNotMF, hAmen, hNotQD⟩ :=
    GroupApproximation.AmenableTraceTheorem.manuscriptAmenableNonquasidiagonalTraceCore
  exact ⟨GroupApproximation.LiteralNonMFLinearWitness.WitnessGroup, inferInstance, inferInstance,
    hSofic, fun hL => hNotMF
      ((literalMF_iff_isOperatorMF GroupApproximation.LiteralNonMFLinearWitness.WitnessGroup).mp hL), hNotMF, hAmen, hNotQD⟩

end IntroAmenable
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.IntroAmenable.manuscriptSentence_soficNonMFSemidirect
#audit_axioms GroupApproximation.Manuscript.NonMF.IntroAmenable.manuscriptSentence_soficNonMFAmenableNonQDTrace
