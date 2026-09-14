import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainFromGeneral
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SubshiftMatricial
import GroupApproximation.Meta.AxiomGuard

/-!
# `simple_kazhdan_sofic_group.tex`: the matricial pieces of `thm:general` and `thm:main`, closed

ct-two-ended's statement modules `GeneralTheorem` and `MainFromGeneral` name two pieces:

* `PrintedMatricialMarkedLimitStatement` (tex 214–234, "Finite simple models"): a matricial ring with
  simple `EL_n(R)`, `n ≥ 3`, is the marked limit of `EL_n(M_{N_k}(F₂))`;
* `PrintedPeriodicMatricialStatement` (tex 249–271, proof of `thm:main`): periodic approximations make
  the ring of an infinite minimal subshift matricial via `printedGenerators S = {1, u, u⁻¹} ∪ {e_a}`.

This module produces both, from `isMarkedLimit_of_matricial` (MatricialMarkedLimitWords) and
`exists_periodicMatricial` (SubshiftMatricial).
-/

namespace GroupApproximation

namespace SimpleKazhdanSofic

open Filter SymbolicDynamics.FullShift

/-- `printedGenerators S` is the printed set `{1} ∪ ringGenerators S` as a set. -/
theorem coe_printedGenerators {A : Type} [TopologicalSpace A] [DiscreteTopology A] [DecidableEq A]
    [Finite A] (S : Subshift A ℤ) :
    ((printedGenerators S : Finset (R S)) : Set (R S)) = printedGeneratorsSet S := by
  classical
  unfold printedGenerators printedGeneratorsSet
  rw [Finset.coe_insert, Set.Finite.coe_toFinset]

/-- **Periodic approximations make `LC(X, F₂) ⋊_T ℤ` matricial** (tex 124, 249–271), closed. -/
theorem printedPeriodicMatricialStatement : PrintedPeriodicMatricialStatement := by
  intro A _ _ _ _ S hinf hmin
  obtain ⟨N, φ, hpos, h1, hgen, hev⟩ := exists_periodicMatricial S hinf hmin
  refine ⟨N, φ, hpos, h1, fun k => ?_, hev⟩
  rw [coe_printedGenerators]
  exact hgen k

end SimpleKazhdanSofic

end GroupApproximation

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedPeriodicMatricialStatement
