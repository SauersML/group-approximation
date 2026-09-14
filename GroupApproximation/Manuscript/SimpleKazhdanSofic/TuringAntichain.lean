import GroupApproximation.Computability.PerfectTreeAntichain
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemDegreeStatements
import GroupApproximation.Meta.AxiomGuard

/-!
# The Turing degrees contain an antichain of size continuum

`simple_kazhdan_sofic_group.tex`, corollary `cor:wp`, proof:

> The Turing degrees contain an antichain of size continuum [Odifreddi, Chapter V], and the groups
> `G_{X_α}` with `α` of these degrees are as claimed.

This module proves skf-degrees' `PrintedTuringAntichainContinuum` without a literature input.  The
proof is the perfect-tree finite-extension construction of `Computability.PerfectTreeAntichain`: it
uses the oracle use principle (`OracleUse.mem_eval_of_agreeBelow`) and the finite-extension step
(`OracleUse.exists_diag`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

/-- The oracle of a set is the total oracle of `OracleUse`. -/
theorem charOracle_eq_setOracle (B : Set ℕ) : charOracle B = OracleUse.setOracle B :=
  rfl

/-- **cor:wp, proof: the Turing degrees contain an antichain of size continuum.** -/
theorem printedTuringAntichainContinuum : PrintedTuringAntichainContinuum := by
  obtain ⟨F, hF, hanti⟩ := OracleUse.exists_turing_antichain_continuum
  refine ⟨F, hF, fun B hB C hC h => hanti B hB C hC ?_⟩
  rwa [charOracle_eq_setOracle, charOracle_eq_setOracle] at h

end SimpleKazhdanSofic
end GroupApproximation

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedTuringAntichainContinuum
