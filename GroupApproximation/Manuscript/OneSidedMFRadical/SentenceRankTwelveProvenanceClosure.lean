import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration

/-!
# Sentence-level closure for the rank-twelve provenance

This file names the exact mathematical content of census row 223.  The
three coordinate layers are exposed explicitly: the inner `Fin 3` is the
Kazhdan corner, adjoining the middle `Fin 2` produces the `6 × 6` half on
which the Whitehead word is formed, and adjoining the outer `Fin 2` produces
the printed `12 × 12` matrix.  The equality in the last conjunct is the
literal six-elementary Whitehead factorization used by the manuscript.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankTwelveEndpoint

open scoped commutatorElement

/-- **Sentence 223.**  The printed dimension `12` is the outer doubling of a
`6 × 6` Whitehead half built from the `3 × 3` Kazhdan corner, and the printed
stable letter is exactly the six-factor Whitehead word. -/
theorem manuscriptSentence223_rankTwelveProvenance :
    Fintype.card (Fin 3) = 3 ∧
      Fintype.card (Fin 2 × Fin 3) = 6 ∧
      Fintype.card (Fin 2 × (Fin 2 × Fin 3)) = 12 ∧
      HasKazhdanPropertyT.{0, 0} corner ∧
      RankTwelve.tauUnit leavittFamily =
        elementaryUnit 0 1 (by decide) (RankTwelve.shift leavittFamily) *
          elementaryUnit 1 0 (by decide)
            (-(RankTwelve.shiftInv leavittFamily)) *
          elementaryUnit 0 1 (by decide) (RankTwelve.shift leavittFamily) *
          elementaryUnit 1 0 (by decide) 1 *
          elementaryUnit 0 1 (by decide) (-1) *
          elementaryUnit 1 0 (by decide) 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num,
    corner_hasKazhdanPropertyT, ?_⟩
  exact tauUnit_eq_six_elementary

end RankTwelveEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
