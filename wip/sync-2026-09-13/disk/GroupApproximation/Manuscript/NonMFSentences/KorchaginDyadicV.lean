import GroupApproximation.Manuscript.NonMFSentences.KorchaginDirectLimit
import GroupApproximation.Manuscript.NonMFSentences.DyadicReductionSeparation
import GroupApproximation.Meta.AxiomGuard

/-!
# `V` is MF by Korchagin's Corollary 10

`non_mf_groups_exist.tex`, the remark after `prop:max-infinite` (origin/main,
lines 780-781):

> … and reduction modulo odd integers separates its elements, so `V` is
> residually finite and MF~\cite[Corollary~10]{Korchagin}.

`DyadicReductionSeparation.manuscriptSentence_reductionModuloOddRFAndMF` proves
the clause with the MF half from `isOperatorMF_of_residuallyFinite`.  This
module proves the MF half through the cited result itself,
`KorchaginDirectLimit.korchaginCorollaryTen` ("Residually MF-groups are
MF-groups"): the finite quotients of `V` are MF, so `V` is residually MF.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences

open Manuscript.OneSidedMFRadical.MaxInfiniteConverse
open KorchaginDirectLimit

/-- **Printed** (tex lines 780-781): "so `V` is residually finite and
MF~\cite[Corollary~10]{Korchagin}". -/
def PrintedDyadicVResiduallyFiniteAndMFCorollaryTen : Prop :=
  Group.ResiduallyFinite V ∧ IsOperatorMF V

theorem manuscriptSentence_dyadicVResiduallyFiniteAndMFCorollaryTen :
    PrintedDyadicVResiduallyFiniteAndMFCorollaryTen := by
  haveI := residuallyFinite_of_reductionModuloOdd
  exact ⟨residuallyFinite_of_reductionModuloOdd,
    korchaginCorollaryTen V isResiduallyMF_of_residuallyFinite⟩

end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.NonMFSentences.manuscriptSentence_dyadicVResiduallyFiniteAndMFCorollaryTen
