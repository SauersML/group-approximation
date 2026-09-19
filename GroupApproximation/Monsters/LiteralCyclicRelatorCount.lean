import GroupApproximation.Monsters.LiteralCyclicCalibration
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# The cyclic calibration presentation has exactly seven relators

The manuscript's cyclic-base calibration group `E_BS` is displayed with three
generators and seven relators.  As for the literal eight-generator
presentation, the count is a theorem rather than a reading of the display:
the seven printed words have to be pairwise distinct in `FreeGroup (Fin 3)`.

The calibration file installs a classical `DecidableEq` instance, so its
`Finset` of relators is not computable there.  Here the same seven words are
re-presented as a `List`, shown duplicate free by kernel evaluation of the
reduced-word normal form, and the count is transferred through
`List.toFinset_card_of_nodup`.
-/

namespace GroupApproximation
namespace LiteralCyclicCalibration

/-- The seven displayed relators of `E_BS`, in the printed order. -/
def relatorList : List (FreeGroup Generator) :=
  [stableRelator, lampSqRelator, lampGammaRelator, markedSqRelator,
    markedGammaRelator, markedStableRelator, markedLampRelator]

@[simp] theorem relatorList_length : relatorList.length = 7 := rfl

/-- The seven displayed relators are pairwise distinct. -/
theorem relatorList_nodup : relatorList.Nodup :=
  List.Nodup.of_map FreeGroup.toWord (by decide)

theorem mem_relators_iff_mem_list (r : FreeGroup Generator) :
    r ∈ relators ↔ r ∈ relatorList := by
  simp only [relators, relatorList, List.mem_toFinset]

theorem relators_eq_toFinset : relators = relatorList.toFinset := by
  ext r
  rw [List.mem_toFinset]
  exact mem_relators_iff_mem_list r

/-- **The cyclic calibration presentation has exactly seven relators.** -/
theorem relators_card : relators.card = 7 := by
  rw [relators_eq_toFinset,
    List.toFinset_card_of_nodup relatorList_nodup, relatorList_length]

/-- The printed shape of the calibration presentation: three generators and
seven relators. -/
theorem manuscriptCyclicCalibrationCounts :
    Fintype.card Generator = 3 ∧ relators.card = 7 :=
  ⟨by decide, relators_card⟩

end LiteralCyclicCalibration
end GroupApproximation
