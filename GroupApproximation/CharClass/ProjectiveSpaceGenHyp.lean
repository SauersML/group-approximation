import GroupApproximation.CharClass.ProjectiveSpaceRingEntry
import GroupApproximation.CharClass.CohomologyChartSplit
import GroupApproximation.CharClass.SteenrodCupOne
import GroupApproximation.CharClass.ChernEulerSqOne

/-!
# The generation hypothesis, from the ring statement

`cc-cohom-api`'s general-rank induction consumes one statement about the fibre and
no more: that cupping with the degree-two generator is surjective in every degree
of `H^*(ℂP^d; F₂)`.  That is strictly weaker than a basis, and in particular it
does not mention the top power.

It follows from the ring statement I published as the frozen interface, and the
derivation is a case split.  Outside the even degrees up to twice the dimension
the group vanishes and zero works; inside, the group is a line, so the class is
either zero or the corresponding power, and a power is the generator cupped with
the power below it.

The one wrinkle is that `cup` puts the generator on the left while `cupPowE`
builds it on the right, so `cup_comm` appears; and `2 + 2j` is not definitionally
`2j + 2`, so the transports are real rather than cosmetic.

## Main declarations

* `cpGenHyp_of_cupPowE_ne_zero` — **the generation hypothesis, from the ring**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open CategoryTheory

noncomputable section

/-- **Cupping with the generator is surjective**, given that the powers up to the
dimension are nonzero.  This is the only thing `cc-cohom-api`'s general-rank
induction asks of the fibre. -/
theorem cpGenHyp_of_cupPowE_ne_zero (d : ℕ)
    (hne : ∀ (hd : 1 ≤ d) (m : ℕ), m ≤ d → cupPowE (cpGen d hd) m ≠ 0) :
    KnCP.CPGenHyp d := by
  intro hd k c
  by_cases hk : ∃ j : ℕ, 2 + k = 2 * (j + 1) ∧ j + 1 ≤ d
  · obtain ⟨j, he, hjd⟩ := hk
    have hkj : k = 2 * j := by omega
    subst hkj
    rcases eq_zero_or_eq_cupPowE_cpGen_of_ne d hd hjd (hne hd (j + 1) hjd)
      (cohCast he c) with h0 | h1
    · exact ⟨0, by rw [cup_zero]; exact (cohCast_eq_zero_iff he c).mp h0⟩
    · refine ⟨cupPowE (cpGen d hd) j, ?_⟩
      have h2 : c = cohCast he.symm (cupPowE (cpGen d hd) (j + 1)) := by
        rw [← h1, cohCast_cohCast, cohCast_self]
      rw [h2]
      show cohCast he.symm (cup (cupPowE (cpGen d hd) j) (cpGen d hd)) = _
      rw [cup_comm, cohCast_cohCast]
      exact cohCast_self _ _
  · refine ⟨0, ?_⟩
    rw [cup_zero]
    refine eq_zero_CP_of_ne d (2 + k) ?_ c
    intro n hn hcontra
    exact hk ⟨n - 1, by omega, by omega⟩

end

end CPn
end CharClass
end GroupApproximation
