import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedLeavittEquations

/-!
# The printed complementary coefficients `p` and `q`

The manuscript names both coefficients in census row 201.  The development
already names `q`; this file also names the paper's `p` and states rows
201--204 using those literal names.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace RankTwelveEndpoint

/-- The manuscript coefficient `p = s₀t₀`. -/
def p : R := leavittFamily.p0

/-- **Sentence-census row 201.**  The two named coefficients are exactly the
two range idempotents of the binary Leavitt family. -/
theorem manuscriptPQDefinitions :
    p = leavittFamily.s0 * leavittFamily.t0 ∧
      q = leavittFamily.s1 * leavittFamily.t1 := by
  exact ⟨rfl, rfl⟩

/-- **Sentence-census rows 202--204.**  The displayed complementary-idempotent
and sandwich equations hold for the literal `p,q`, and the latter forces the
printed nonvanishing conclusion for `q`. -/
theorem manuscriptPQEquations :
    p + q = 1 ∧
      leavittFamily.t1 * q * leavittFamily.s1 = 1 ∧
      q ≠ 0 := by
  exact ⟨by simp [p, q, leavittFamily.p0_add_p1],
    by simp [q],
    q_ne_zero⟩

end RankTwelveEndpoint
end OneSidedMFRadical
end Manuscript
end GroupApproximation
