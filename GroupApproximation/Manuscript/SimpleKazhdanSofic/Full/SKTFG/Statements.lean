import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.StepanovMatui.MatuiSimplicity
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemDegreeStatements
import GroupApproximation.Meta.AxiomGuard

/-!
# Grigorchuk–Medynets for derived topological full groups (SK row `e5932a45f053`)

`simple_kazhdan_sofic_group.tex`, l.724–726:

> For derived topological full groups, Grigorchuk and Medynets proved that the word problem is
> solvable if and only if `L(X)` is recursive [GMpres, Thm 1.1(3)].

The paper's argument does not use this result: the sentence credits the analogue of `cor:wp`,
which the paper proves for its groups `G_X` (`Full.SK13.wp_solvable_iff_recursive`). Here the
group is the derived topological full group `derivedFullGroupSubshift S = ⁅[[σ]], [[σ]]⁆` of
`Full.StepanovMatui.Matui`. That is the same group whose simplicity closes the neighboring
attribution row `3eaee0a2dc7e` (Matui, tex l.307–309), in
`Full.StepanovMatui.Matui.printedMatuiRemark`.

Two named propositions, neither proved yet:

* `DerivedFullGroupSubshiftFGStatement`: for an infinite minimal subshift, `[[σ]]'` is finitely
  generated (Matui, Thm 5.4, the direction from subshifts to finite generation). Nothing on main
  proves it.
* `GrigorchukMedynetsWordProblemStatement`: `[[σ]]'` has a finite generating family whose word
  problem is solvable if and only if `L(X)` is recursive. The two reductions should follow
  `Full.SK13.wp_reduces_to_language` and `Full.SK13.language_reduces_to_wp`.
-/

namespace GroupApproximation.Full.SKTFG

open SymbolicDynamics.FullShift
open GroupApproximation.Full.StepanovMatui.Matui

/-- **Matui, Theorem 5.4** (finite generation, for the row `e5932a45f053`): the derived
topological full group of the shift of an infinite minimal subshift is finitely generated. -/
def DerivedFullGroupSubshiftFGStatement : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Finite A] (S : Subshift A ℤ),
    Infinite S.carrier → GroupApproximation.SimpleKazhdanSofic.IsMinimal S →
      Group.FG ↥(derivedFullGroupSubshift S)

/-- **Grigorchuk–Medynets, Theorem 1.1(3)** (row `e5932a45f053`, tex l.724–726). For an infinite
minimal subshift `X` over a finite alphabet, `[[σ_X]]'` has a finite generating family whose word
problem is solvable if and only if the language `L(X)` is recursive. The oracles are those of the
paper's own `cor:wp`. -/
def GrigorchukMedynetsWordProblemStatement : Prop :=
  ∀ (A : Type) [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [DecidableEq A]
    [Primcodable A] (S : Subshift A ℤ), Infinite S.carrier →
    GroupApproximation.SimpleKazhdanSofic.IsMinimal S →
    ∃ (k : ℕ) (s : Fin k → ↥(derivedFullGroupSubshift S)),
      Subgroup.closure (Set.range s) = ⊤ ∧
      (Partrec (GroupApproximation.SimpleKazhdanSofic.wordProblemOracle s) ↔
        Partrec (GroupApproximation.SimpleKazhdanSofic.languageOracle S))

end GroupApproximation.Full.SKTFG
