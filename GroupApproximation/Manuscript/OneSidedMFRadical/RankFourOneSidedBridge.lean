import GroupApproximation.Manuscript.OneSidedMFRadical.RankFourConfiguration
import GroupApproximation.Leavitt.OneSidedCompressorDefect

/-!
# The two rank-four developments are about the same objects

`Leavitt.RankFourCompressors` and `Leavitt.OneSidedCompressor` both realize the
compressor of the printed proof of `thm:full-defect-ring`.  The first is stated
for a ring carrying a binary Leavitt family and came first; the second is
stated for a bare one-sided inverse pair `ts = 1`, which is the printed
hypothesis, and is therefore the more general of the two.
`Manuscript.OneSidedMFRadical.RankFourEndpoints` and `RankFourConfiguration`
were built on the first.

This module proves that at a binary Leavitt family the two agree, object by
object, so that no statement proved on one side has to be reproved on the
other.  Every identification below is definitional except the two that involve
the complementary idempotent: `RankFour` spells it `L.p1 = s₁t₁` and
`OneSidedCompressor` spells it `e = 1 - s₀t₀`, and those are equal by
`p₀ + p₁ = 1`, not by unfolding.

The bridge runs in the useful direction.  `OneSidedCompressor` proves
`printedDefectRoot_mem_printedDefect` for every one-sided pair over every
unital ring; the manuscript's group is the instance at
`ofLeavittFamily UniversalLeavitt.family`, and
`printedDefect_core_eq_top` below is the rank-four saturation statement in
`OneSidedCompressor`'s own vocabulary.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankFourEndpoint

open scoped commutatorElement

section Generic

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-- **The two rank-four corners are the same subgroup.**  Both are the closure
of the elementary roots at index pairs drawn from `Fin.castSucc '' (Fin 3)`. -/
theorem genericCorner_eq_core : genericCorner A = OneSidedCompressor.core A :=
  rfl

/-- **The two rank-four compressors are the same element.**  Both are the same
twelve-transvection word `u = u₃u₂u₁` with
`uᵢ = e₄ᵢ(t-1) eᵢ₄(1) e₄ᵢ(s-1) eᵢ₄(-t)`; the Leavitt version reads `s`, `t` off
the zeroth Leavitt pair, which is exactly what `ofLeavittFamily` does. -/
theorem compressor_eq_oneSidedCompressor :
    RankFour.compressor L =
      OneSidedCompressor.compressor (OneSidedCompressor.ofLeavittFamily L) :=
  rfl

/-- **The two rank-four centralizer marks are the same element.**  Here the
identification is not definitional: the mark's coefficient is the
complementary idempotent, spelled `s₁t₁` on one side and `1 - s₀t₀` on the
other. -/
theorem genericMark_eq_centralMark :
    genericMark L =
      OneSidedCompressor.centralMark (OneSidedCompressor.ofLeavittFamily L) := by
  rw [OneSidedCompressor.centralMark_eq_commutator,
    OneSidedCompressor.e_ofLeavittFamily]
  rfl

end Generic

/-! ## The identifications at the manuscript's ring -/

theorem corner_eq_core : corner = OneSidedCompressor.core R := rfl

theorem u_eq_oneSidedCompressor :
    u = OneSidedCompressor.compressor
      (OneSidedCompressor.ofLeavittFamily leavittFamily) :=
  compressor_eq_oneSidedCompressor leavittFamily

theorem c_eq_centralMark :
    c = OneSidedCompressor.centralMark
      (OneSidedCompressor.ofLeavittFamily leavittFamily) :=
  genericMark_eq_centralMark leavittFamily

theorem ell_eq_printedEll : ell = OneSidedCompressor.printedEll R := rfl

theorem defect_eq_printedDefectRoot :
    defect = OneSidedCompressor.printedDefectRoot
      (OneSidedCompressor.ofLeavittFamily leavittFamily) := by
  show defect =
    elementaryRoot (OneSidedCompressor.coreIdx 0) (OneSidedCompressor.coreIdx 2)
      (OneSidedCompressor.coreIdx_injective.ne OneSidedCompressor.zeroNeTwo)
      (OneSidedCompressor.ofLeavittFamily leavittFamily).e
  rw [OneSidedCompressor.e_ofLeavittFamily]
  rfl

/-- **The rank-four saturation, in `OneSidedCompressor`'s vocabulary.**  At the
manuscript's ring the printed defect of the printed core is everything.  This
is `RankFourEndpoint.printedDefect_eq_top_of_configuration` transported along
`corner_eq_core`; the transport is definitional, so nothing is reproved. -/
theorem printedDefect_core_eq_top :
    printedDefect (OneSidedCompressor.core R) = ⊤ := by
  rw [← corner_eq_core]
  exact printedDefect_eq_top_of_configuration printedDefectConfiguration

end RankFourEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
