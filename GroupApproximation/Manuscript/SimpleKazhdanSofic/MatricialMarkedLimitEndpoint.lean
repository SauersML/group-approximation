import GroupApproximation.Manuscript.SimpleKazhdanSofic.GeneralTheorem
import GroupApproximation.Manuscript.SimpleKazhdanSofic.MatricialMarkedLimitWords
import GroupApproximation.Meta.AxiomGuard

/-!
# `simple_kazhdan_sofic_group.tex`, "Finite simple models": the marked-limit piece of `thm:general`, closed

ct-two-ended's `GeneralTheorem` names the piece `PrintedMatricialMarkedLimitStatement` (tex 214–234): a
matricial ring (`IsMatricialVia`, sizes `N_k ≥ 1`) with simple `EL_n(R)`, `n ≥ 3`, marked by the
`e_ij(s)`, `s ∈ S`, is the limit of `EL_n(M_{N_k}(F₂))` marked by the `e_ij(φ_k(s))`.  This module
produces it from `isMarkedLimit_of_matricial` (MatricialMarkedLimitWords).
-/

namespace GroupApproximation

namespace SimpleKazhdanSofic

open Filter

/-- **"Finite simple models"** (tex 214–234), closed. -/
theorem printedMatricialMarkedLimitStatement : PrintedMatricialMarkedLimitStatement := by
  intro R _ S hS1 hS N φ hφ n hn hsimple
  obtain ⟨hpos, h1, hgen, hev⟩ := hφ
  haveI := hsimple
  exact isMarkedLimit_of_matricial S N φ hn hS1 hS h1 hgen hev (Eventually.of_forall hpos)

end SimpleKazhdanSofic

end GroupApproximation

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedMatricialMarkedLimitStatement
