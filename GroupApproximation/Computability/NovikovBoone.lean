import GroupApproximation.Computability.BooneWordProblem
import GroupApproximation.Computability.BooneGroupFinitePresentation

/-!
# Novikov--Boone, in full

> There is a **finitely presented** group whose word problem is undecidable.

Unconditionally, with no hypothesis and no literature input.  The undecidable
source is Mathlib's `ComputablePred.halting_problem`; every step between it and
here is in this repository.

The two halves arrived separately and this file is their conjunction.

* `BooneWordProblem.exists_group_wordProblem_not_computablePred` is the
  word-problem half: Simpson's Theorem 8 (`conj_k_finalTw_eq_iff`) turns a
  machine's halting set into triviality of an explicit sequence of words in
  `G_M`, and `ModularMachineUndecidable` supplies a modular machine whose
  halting set is not computable.
* `BooneGroupFinitePresentation.finalGroup_isFinitelyPresented` is the
  adjective: `G_M` is finitely presented, because the base group is
  `⟨t, x, y | xy = yx⟩`, each `G_{ab}^{MN}` is three-generated, `⟨t⟩'` is
  finitely generated in the tower (though not in the base group), and an HNN
  extension of a finitely presented group along finitely generated associated
  subgroups is finitely presented (`Algebra.HNNFinitePresentation`).

Both are about the *same* group, `FinalGroup mm hM`, so nothing has to be
transported: the theorem below re-runs the word-problem argument with the
finite-presentation fact carried alongside.

## What this closes

Item **D4** of the debt table in
`GroupApproximation.Computability.AdianRabinMarkovProperty`, and with it the
last stage of the roadmap in `Computability.BooneGroupBase`.  The route was
Aanderaa--Cohen modular machines in Simpson's writeup rather than
Boone--Britton; Britton's Lemma itself is used in exactly one place, the
good-subgroup lemma of S4.

What remains before the manuscript's `cor:undecidable` loses its hypothesis is
**D5**, the effective Adian--Rabin construction, which is a different
construction and consumes this theorem as its source.
-/

namespace GroupApproximation
namespace BooneGroup

open Computability

/-- **Novikov--Boone.**  There is a finitely presented group and a sequence of
words in it for which triviality is not decidable.

Unconditional: no hypothesis, and no literature input. -/
theorem exists_finitelyPresented_wordProblem_not_computablePred (n : ℕ) :
    ∃ (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧
        ∃ g : ℕ → G, ¬ ComputablePred fun m : ℕ => g m = 1 := by
  obtain ⟨mm, f, hf⟩ := exists_modularMachine_halting_not_computablePred n
  have hM : (mm.size : ℤ) ≠ 0 := by
    have h := mm.size_pos
    exact_mod_cast h.ne'
  refine ⟨FinalGroup mm hM, inferInstance, finalGroup_isFinitelyPresented mm hM,
    fun m => (HNNExtension.t⁻¹ * finalTw mm hM (((f m).1 : ℤ), ((f m).2 : ℤ)) *
      HNNExtension.t) * (finalTw mm hM (((f m).1 : ℤ), ((f m).2 : ℤ)))⁻¹, ?_⟩
  intro hcomp
  refine hf ?_
  have hEq : (fun m : ℕ => mm.Halts (f m))
      = fun m : ℕ => ((HNNExtension.t⁻¹ *
          finalTw mm hM (((f m).1 : ℤ), ((f m).2 : ℤ)) * HNNExtension.t) *
            (finalTw mm hM (((f m).1 : ℤ), ((f m).2 : ℤ)))⁻¹ : FinalGroup mm hM) = 1 := by
    funext m
    rw [mul_inv_eq_one]
    exact propext (conj_k_finalTw_eq_iff mm hM (f m)).symm
  exact hEq ▸ hcomp

/-- The manuscript's form: existence alone, with every binder after the
colon.  Weaker than the parametrised statement above, which is why it is a
separate proposition rather than a restatement of it. -/
theorem exists_finitelyPresented_wordProblem_undecidable :
    ∃ (G : Type) (_ : Group G),
      Group.IsFinitelyPresented G ∧
        ∃ g : ℕ → G, ¬ ComputablePred fun m : ℕ => g m = 1 :=
  exists_finitelyPresented_wordProblem_not_computablePred 0

end BooneGroup
end GroupApproximation
