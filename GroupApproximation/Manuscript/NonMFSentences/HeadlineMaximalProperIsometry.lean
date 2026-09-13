import GroupApproximation.Manuscript.OneSidedMFRadical.UnitGroupHeadline
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingProperIsometry
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:headline`: the maximal algebra of the unit group contains a proper isometry

`non_mf_groups_exist.tex`, Theorem `thm:headline` (`\label{thm:headline}`, tex 233–241), last clause:

> ... while `C^*_{\max}(H)` is not finite: it contains a proper isometry.

`UnitGroupHeadline.manuscriptUnitGroupHeadline` carries this clause as the strict projection configuration
`P < vPv*` of `prop:max-infinite` together with `¬ IsDedekindFiniteMonoid (MaximalGroupCStar Rˣ)`.  The printed
words name a proper isometry, so this module states the clause literally: an element `v` of `C^*_{\max}(R^×)` with
`v⋆v = 1` that is not a unit.

The route is the printed one.  `prop:max-infinite` applies to the printed configuration carried to the unit group:
the image `unitCorner` of the rank-four corner has property (T), and conjugation by the image `unitCompressor` of
the printed compressor maps it strictly into itself.  `FullDefectRing.properIsometry_of_strictCompression` is
`prop:max-infinite` for a countable-free group statement, proved in the repository; nothing here is assumed.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace HeadlineMaximalProperIsometry

open OneSidedMFRadical.RankFourEndpoint
open OneSidedMFRadical.UnitGroupHeadline

/-- **tex 238–239**, the maximal-algebra clause of `thm:headline` as printed: `C^*_{\max}(H)` is not finite, and it
contains a proper isometry.  Here `H = R^×` with `R = L_{𝔽₂}(1,2)`. -/
def PrintedHeadlineMaximalProperIsometry : Prop :=
  ¬ IsDedekindFiniteMonoid (MaximalGroupCStar Rˣ) ∧
    ∃ v : MaximalGroupCStar Rˣ, star v * v = 1 ∧ ¬ IsUnit v

/-- **The maximal algebra of the headline group contains a proper isometry**, by `prop:max-infinite` at the printed
Kazhdan corner and compressor of the unit group. -/
theorem manuscriptSentence_headlineMaximalProperIsometry :
    PrintedHeadlineMaximalProperIsometry := by
  obtain ⟨hiso, hfin, -⟩ :=
    OneSidedMFRadical.FullDefectRing.properIsometry_of_strictCompression
      unitCorner unitCompressor unitCorner_hasKazhdanPropertyT unitCorner_conj_lt
  exact ⟨hfin, hiso⟩

end HeadlineMaximalProperIsometry
end NonMFSentences
end Manuscript
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.HeadlineMaximalProperIsometry.manuscriptSentence_headlineMaximalProperIsometry
