import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveConfiguration

/-!
# Entrywise insertion of a Whitehead off-diagonal block

This file names the zero-product calculation used in census row 215 when a
`6×6` off-diagonal block is inserted one entry at a time into a `12×12`
Whitehead factor.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankTwelveEndpoint

section

/-- Two contributions to the same outer off-diagonal block multiply to zero
in either order.  This is the literal pairwise-zero-product assertion from
the manuscript. -/
theorem manuscriptWhiteheadOffDiagonalBlocksPairwiseZero
    (b c : Fin 2) (hbc : b ≠ c) (Z W : RankTwelve.Half R) :
    Matrix.single b c Z * Matrix.single b c W = 0 ∧
      Matrix.single b c W * Matrix.single b c Z = 0 := by
  exact ⟨Matrix.single_mul_single_of_ne
      (c := Z) b c b hbc.symm W,
    Matrix.single_mul_single_of_ne
      (c := W) b c b hbc.symm Z⟩

/-- Flattening to literal `12×12` matrices preserves both zero products. -/
theorem manuscriptFlattenedWhiteheadBlocksPairwiseZero
    (b c : Fin 2) (hbc : b ≠ c) (Z W : RankTwelve.Half R) :
    flat12 (Matrix.single b c Z) * flat12 (Matrix.single b c W) = 0 ∧
      flat12 (Matrix.single b c W) * flat12 (Matrix.single b c Z) = 0 := by
  obtain ⟨hZW, hWZ⟩ :=
    manuscriptWhiteheadOffDiagonalBlocksPairwiseZero b c hbc Z W
  constructor
  · rw [← map_mul, hZW, map_zero]
  · rw [← map_mul, hWZ, map_zero]

/-- Entrywise insertion turns addition of two `6×6` contributions into
multiplication of the corresponding block-unipotent factors. -/
theorem manuscriptWhiteheadEntryInsertionProduct
    (b c : Fin 2) (hbc : b ≠ c) (Z W : RankTwelve.Half R) :
    elementaryUnit b c hbc Z * elementaryUnit b c hbc W =
      elementaryUnit b c hbc (Z + W) :=
  elementaryUnit_mul b c hbc Z W

/-- **Sentence-census row 215.**  The exact zero-product and entry-insertion
identities are accompanied by the conclusion used for each block-unipotent
factor of the Whitehead word: after flattening, it lies in `EL₁₂(R)`. -/
theorem manuscriptWhiteheadEntrywiseElementaryRoute
    (b c : Fin 2) (hbc : b ≠ c) (Z W : RankTwelve.Half R) :
    (Matrix.single b c Z * Matrix.single b c W = 0 ∧
      Matrix.single b c W * Matrix.single b c Z = 0) ∧
      elementaryUnit b c hbc Z * elementaryUnit b c hbc W =
        elementaryUnit b c hbc (Z + W) ∧
      flat12Units (elementaryUnit b c hbc Z) ∈
        elementaryGroup (Fin 12) R := by
  exact ⟨manuscriptWhiteheadOffDiagonalBlocksPairwiseZero b c hbc Z W,
    manuscriptWhiteheadEntryInsertionProduct b c hbc Z W,
    flat12Units_elementary_mem b c hbc Z⟩

end

end RankTwelveEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
