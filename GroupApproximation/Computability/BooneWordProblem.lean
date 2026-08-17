import GroupApproximation.Computability.BooneGroupGoodness
import GroupApproximation.Computability.ModularMachineUndecidable

/-!
# Novikov--Boone: a group whose word problem is not decidable

Simpson's Theorem 8 (`BooneGroupGoodness.conj_k_finalTw_eq_iff`) is a
biconditional between a word in the generators of `G_M` and a fact about the
machine `M`:

    `k⁻¹ t(α,β) k = t(α,β)`   in   `G_M`    ↔    `(α,β)` halts.

It holds for *every* modular machine, and by itself says nothing about
decidability.  S9 (`Computability.ModularMachineUndecidable`) supplies a machine
whose halting set is not computable, and the two together give a group in which
deciding whether a word is trivial is not possible.

The theorem below is the word-problem half of Novikov--Boone, stated for the
group as constructed.  **S8, the other half, is also proved**: Mathlib indeed
has no closure property for `Group.IsFinitelyPresented` under HNN extensions,
and `Algebra.HNNFinitePresentation` supplies one, from which
`BooneGroupFinitePresentation.finalGroup_isFinitelyPresented` gives that `G_M`
is finitely presented.  `Computability.NovikovBoone` is the conjunction of the
two, and is the classical statement.
-/

namespace GroupApproximation
namespace BooneGroup

open Computability

/-- **Novikov--Boone, the word-problem half.**  There is a group and a sequence
of words in it for which triviality is not decidable.

Unconditional: no hypothesis, and no literature input.  The undecidable source
is Mathlib's `ComputablePred.halting_problem`; everything between it and here
is in this repository. -/
theorem exists_group_wordProblem_not_computablePred (n : ℕ) :
    ∃ (G : Type) (_ : Group G) (g : ℕ → G),
      ¬ ComputablePred fun m : ℕ => g m = 1 := by
  obtain ⟨mm, f, hf⟩ := exists_modularMachine_halting_not_computablePred n
  have hM : (mm.size : ℤ) ≠ 0 := by
    have h := mm.size_pos
    exact_mod_cast h.ne'
  refine ⟨FinalGroup mm hM, inferInstance,
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

end BooneGroup
end GroupApproximation
