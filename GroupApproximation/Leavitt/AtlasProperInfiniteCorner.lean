import GroupApproximation.Leavitt.PrefixCode

/-!
# The explicit two-child corner in the raw-compressor atlas packet

The hard class-11 prefix pair, together with the scalarized raw swap and comb
compressor, produces the two reduced monomials

`a₀ = s_[1,1,0,0,0] t_[1,1]` and
`a₁ = s_[1,1,1] t_[1,1]`.

This file verifies the load-bearing algebraic conclusion without referring to
the search which found the words: both monomials have initial idempotent
`p_[1,1]`, and their range idempotents are orthogonal.  Thus `p_[1,1]` is a
properly infinite corner in every ring carrying a binary Leavitt family.
-/

namespace GroupApproximation
namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

def atlasBaseWord : List (Fin 2) := [1, 1]
def atlasFirstRangeWord : List (Fin 2) := [1, 1, 0, 0, 0]
def atlasSecondRangeWord : List (Fin 2) := [1, 1, 1]

def atlasFirstIsometry : A :=
  L.wordS atlasFirstRangeWord * L.wordT atlasBaseWord

def atlasFirstReverse : A :=
  L.wordS atlasBaseWord * L.wordT atlasFirstRangeWord

def atlasSecondIsometry : A :=
  L.wordS atlasSecondRangeWord * L.wordT atlasBaseWord

def atlasSecondReverse : A :=
  L.wordS atlasBaseWord * L.wordT atlasSecondRangeWord

theorem atlasFirstReverse_mul_atlasFirstIsometry :
    L.atlasFirstReverse * L.atlasFirstIsometry =
      L.cylinder atlasBaseWord := by
  rw [atlasFirstReverse, atlasFirstIsometry]
  calc
    (L.wordS atlasBaseWord * L.wordT atlasFirstRangeWord) *
        (L.wordS atlasFirstRangeWord * L.wordT atlasBaseWord) =
      L.wordS atlasBaseWord *
        (L.wordT atlasFirstRangeWord * L.wordS atlasFirstRangeWord) *
          L.wordT atlasBaseWord := by noncomm_ring
    _ = L.cylinder atlasBaseWord := by
      rw [L.wordT_mul_wordS_self]
      simp [cylinder]

theorem atlasFirstIsometry_mul_atlasFirstReverse :
    L.atlasFirstIsometry * L.atlasFirstReverse =
      L.cylinder atlasFirstRangeWord := by
  rw [atlasFirstReverse, atlasFirstIsometry]
  calc
    (L.wordS atlasFirstRangeWord * L.wordT atlasBaseWord) *
        (L.wordS atlasBaseWord * L.wordT atlasFirstRangeWord) =
      L.wordS atlasFirstRangeWord *
        (L.wordT atlasBaseWord * L.wordS atlasBaseWord) *
          L.wordT atlasFirstRangeWord := by noncomm_ring
    _ = L.cylinder atlasFirstRangeWord := by
      rw [L.wordT_mul_wordS_self]
      simp [cylinder]

theorem atlasSecondReverse_mul_atlasSecondIsometry :
    L.atlasSecondReverse * L.atlasSecondIsometry =
      L.cylinder atlasBaseWord := by
  rw [atlasSecondReverse, atlasSecondIsometry]
  calc
    (L.wordS atlasBaseWord * L.wordT atlasSecondRangeWord) *
        (L.wordS atlasSecondRangeWord * L.wordT atlasBaseWord) =
      L.wordS atlasBaseWord *
        (L.wordT atlasSecondRangeWord * L.wordS atlasSecondRangeWord) *
          L.wordT atlasBaseWord := by noncomm_ring
    _ = L.cylinder atlasBaseWord := by
      rw [L.wordT_mul_wordS_self]
      simp [cylinder]

theorem atlasSecondIsometry_mul_atlasSecondReverse :
    L.atlasSecondIsometry * L.atlasSecondReverse =
      L.cylinder atlasSecondRangeWord := by
  rw [atlasSecondReverse, atlasSecondIsometry]
  calc
    (L.wordS atlasSecondRangeWord * L.wordT atlasBaseWord) *
        (L.wordS atlasBaseWord * L.wordT atlasSecondRangeWord) =
      L.wordS atlasSecondRangeWord *
        (L.wordT atlasBaseWord * L.wordS atlasBaseWord) *
          L.wordT atlasSecondRangeWord := by noncomm_ring
    _ = L.cylinder atlasSecondRangeWord := by
      rw [L.wordT_mul_wordS_self]
      simp [cylinder]

theorem atlasRangeWords_incomparable :
    ¬ atlasFirstRangeWord <+: atlasSecondRangeWord ∧
      ¬ atlasSecondRangeWord <+: atlasFirstRangeWord := by
  decide

theorem atlasBase_mul_firstRange :
    L.cylinder atlasBaseWord * L.cylinder atlasFirstRangeWord =
      L.cylinder atlasFirstRangeWord := by
  have hw : atlasFirstRangeWord = atlasBaseWord ++ [0, 0, 0] := by decide
  rw [hw]
  unfold cylinder
  calc
    (L.wordS atlasBaseWord * L.wordT atlasBaseWord) *
        (L.wordS (atlasBaseWord ++ [0, 0, 0]) *
          L.wordT (atlasBaseWord ++ [0, 0, 0])) =
      L.wordS atlasBaseWord *
        (L.wordT atlasBaseWord *
          L.wordS (atlasBaseWord ++ [0, 0, 0])) *
            L.wordT (atlasBaseWord ++ [0, 0, 0]) := by noncomm_ring
    _ = L.wordS atlasBaseWord * L.wordS [0, 0, 0] *
        L.wordT (atlasBaseWord ++ [0, 0, 0]) := by
      rw [L.wordT_mul_wordS_append_left]
    _ = L.wordS (atlasBaseWord ++ [0, 0, 0]) *
        L.wordT (atlasBaseWord ++ [0, 0, 0]) := by
      rw [L.wordS_append]

theorem atlasBase_mul_secondRange :
    L.cylinder atlasBaseWord * L.cylinder atlasSecondRangeWord =
      L.cylinder atlasSecondRangeWord := by
  have hw : atlasSecondRangeWord = atlasBaseWord ++ [1] := by decide
  rw [hw]
  unfold cylinder
  calc
    (L.wordS atlasBaseWord * L.wordT atlasBaseWord) *
        (L.wordS (atlasBaseWord ++ [1]) *
          L.wordT (atlasBaseWord ++ [1])) =
      L.wordS atlasBaseWord *
        (L.wordT atlasBaseWord * L.wordS (atlasBaseWord ++ [1])) *
          L.wordT (atlasBaseWord ++ [1]) := by noncomm_ring
    _ = L.wordS atlasBaseWord * L.wordS [1] *
        L.wordT (atlasBaseWord ++ [1]) := by
      rw [L.wordT_mul_wordS_append_left]
    _ = L.wordS (atlasBaseWord ++ [1]) *
        L.wordT (atlasBaseWord ++ [1]) := by
      rw [L.wordS_append]

theorem atlasFirstReverse_mul_atlasSecondIsometry :
    L.atlasFirstReverse * L.atlasSecondIsometry = 0 := by
  have h := atlasRangeWords_incomparable
  rw [atlasFirstReverse, atlasSecondIsometry]
  calc
    (L.wordS atlasBaseWord * L.wordT atlasFirstRangeWord) *
        (L.wordS atlasSecondRangeWord * L.wordT atlasBaseWord) =
      L.wordS atlasBaseWord *
        (L.wordT atlasFirstRangeWord * L.wordS atlasSecondRangeWord) *
          L.wordT atlasBaseWord := by noncomm_ring
    _ = 0 := by
      rw [L.wordT_mul_wordS_of_incomparable _ _ h.1 h.2]
      simp

theorem atlasSecondReverse_mul_atlasFirstIsometry :
    L.atlasSecondReverse * L.atlasFirstIsometry = 0 := by
  have h := atlasRangeWords_incomparable
  rw [atlasSecondReverse, atlasFirstIsometry]
  calc
    (L.wordS atlasBaseWord * L.wordT atlasSecondRangeWord) *
        (L.wordS atlasFirstRangeWord * L.wordT atlasBaseWord) =
      L.wordS atlasBaseWord *
        (L.wordT atlasSecondRangeWord * L.wordS atlasFirstRangeWord) *
          L.wordT atlasBaseWord := by noncomm_ring
    _ = 0 := by
      rw [L.wordT_mul_wordS_of_incomparable _ _ h.2 h.1]
      simp

/-- The exact two-child packet: two algebraic isometries have the same initial
idempotent and orthogonal range idempotents. -/
theorem atlas_properlyInfinite_packet :
    L.atlasFirstReverse * L.atlasFirstIsometry =
        L.cylinder atlasBaseWord ∧
      L.atlasSecondReverse * L.atlasSecondIsometry =
        L.cylinder atlasBaseWord ∧
      L.atlasFirstIsometry * L.atlasFirstReverse =
        L.cylinder atlasFirstRangeWord ∧
      L.atlasSecondIsometry * L.atlasSecondReverse =
        L.cylinder atlasSecondRangeWord ∧
      L.cylinder atlasBaseWord * L.cylinder atlasFirstRangeWord =
        L.cylinder atlasFirstRangeWord ∧
      L.cylinder atlasBaseWord * L.cylinder atlasSecondRangeWord =
        L.cylinder atlasSecondRangeWord ∧
      L.atlasFirstReverse * L.atlasSecondIsometry = 0 ∧
      L.atlasSecondReverse * L.atlasFirstIsometry = 0 := by
  exact ⟨L.atlasFirstReverse_mul_atlasFirstIsometry,
    L.atlasSecondReverse_mul_atlasSecondIsometry,
    L.atlasFirstIsometry_mul_atlasFirstReverse,
    L.atlasSecondIsometry_mul_atlasSecondReverse,
    L.atlasBase_mul_firstRange,
    L.atlasBase_mul_secondRange,
    L.atlasFirstReverse_mul_atlasSecondIsometry,
    L.atlasSecondReverse_mul_atlasFirstIsometry⟩

end LeavittFamily
end GroupApproximation
