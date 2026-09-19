import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.SKTFG.LanguageToWordProblem
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemSolvability
import GroupApproximation.Meta.AxiomGuard

/-!
# Grigorchuk–Medynets for derived topological full groups (SK row `e5932a45f053`)

`simple_kazhdan_sofic_group.tex`, l.724–726:

> For derived topological full groups, Grigorchuk and Medynets proved that the word problem is
> solvable if and only if `L(X)` is recursive [GMpres, Thm 1.1(3)].

For an infinite minimal subshift `X` with a separation radius `R`, the generators `genFam` of
`[[σ_X]]'` over the cylinders on `[0, 2R + 1]` generate it
(`derivedFullGroupSubshift_eq_closure_gens_of_sepRadius`, `closure_range_genFam`), and their word
problem has the Turing degree of `L(X)` (`turingReducible_wordProblem_genFam`,
`turingReducible_language_genFam`).
-/

namespace GroupApproximation.Full.SKTFG

open GroupApproximation.SimpleKazhdanSofic
open GroupApproximation.Full.StepanovMatui.Matui

/-- **Grigorchuk–Medynets, Theorem 1.1(3)**: `GrigorchukMedynetsWordProblemStatement` holds. -/
theorem grigorchukMedynetsWordProblemStatement_holds : GrigorchukMedynetsWordProblemStatement := by
  intro A _ _ _ _ _ S hinf hmin
  obtain ⟨R, hR⟩ := exists_sepRadius S hinf hmin 5
  have hDG := derivedFullGroupSubshift_eq_closure_gens_of_sepRadius S hinf hmin hR
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin
    ((Finset.Icc (0 : ℤ) ((2 * R + 1 : ℕ) : ℤ) → A) × alternatingGroup (Fin 5))
  exact ⟨k, genFam S hDG e, closure_range_genFam S hDG e,
    partrec_iff_of_turingEquivalent ⟨turingReducible_wordProblem_genFam S hinf hmin hDG e,
      turingReducible_language_genFam S e hinf hmin hR le_rfl hDG⟩⟩

end GroupApproximation.Full.SKTFG

#audit_closed_axioms GroupApproximation.Full.SKTFG.grigorchukMedynetsWordProblemStatement_holds
