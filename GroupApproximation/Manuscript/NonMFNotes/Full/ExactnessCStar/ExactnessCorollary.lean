import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessCStar.ExactnessAssembly
import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessGHW.GHWAssembly

/-!
# Exactness of the reduced group C⋆-algebra of the literal marked group

Source: `non_mf_group_notes.tex`, section `sec:Esofic`, paragraph
"Exactness", last sentence: the literal marked group `E` is exact, hence
`C*_r(E)` is exact \cite{KWExact}.

* `reducedGroupCStar_markedGroup_exact` --- `IsExactCStar (C*_r(E))`, from
  `Full.NN09b.markedGroup_isExactGroup` (property A of `E`) and
  `isExactCStar_reducedGroupCStar_of_hasPropertyA`.
-/

namespace GroupApproximation.Full.NN09c

open GroupApproximation.CStarTensor GroupApproximation.ReducedGroupCStarTrace

universe v

/-- **The reduced group C⋆-algebra of the literal marked group is exact.**
`non_mf_group_notes.tex`, section `sec:Esofic`, paragraph "Exactness"
\cite{KWExact}. -/
theorem reducedGroupCStar_markedGroup_exact :
    IsExactCStar.{v} (ReducedGroupCStar LiteralNonMFPresentation.MarkedGroup) :=
  isExactCStar_reducedGroupCStar_of_hasPropertyA Full.NN09b.markedGroup_isExactGroup

end GroupApproximation.Full.NN09c
