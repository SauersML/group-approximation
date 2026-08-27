import GroupApproximation.Computability.BooneGroupCode
import GroupApproximation.Computability.ModularMachineConfigHalting
import GroupApproximation.Computability.AdianRabinWordProblem
import GroupApproximation.Computability.MarkovReductionInterface

/-!
# The uniform word problem on codes, reduced to a word map

`D4'` asks for `¬ComputablePred wordProblemPred`.  Three of its four pieces are
on `main`:

* the undecidable source in configuration form,
  `ModularMachineConfigHalting.exists_modularMachine_config_halting_not_computablePred`;
* a code that provably presents `G_M`, `BooneGroupCode.finalGroupCodeEquiv`;
* coded triviality as a decidable search,
  `CodedWordTriviality.wordOf_eq_one_iff_exists_steps`.

The fourth is the word map: a computable `ℕ × ℕ → List (ℕ × Bool)` sending a
configuration to its word in the code's numbering, together with the agreement
proof.  This module is the join, written ahead of it so that supplying the map
closes `D4'` by instantiation rather than by another argument.

The join is worth stating separately for the reason that has bitten this
development twice: when two lanes converge, the capstone is often a conjunction
nobody wrote, and it is easy to believe the endpoint follows while no
declaration says so.  `not_computablePred_wordProblemPred_of_boone_words` says
so, and it threads a **single** machine through both halves --- two existentials
could otherwise choose different machines, and the words are attached to the
configurations of one.
-/

namespace GroupApproximation
namespace Computability

open BooneGroup AdianRabinWordProblem

/-- **The reduction, for an arbitrary code and word map.**  If some machine's
configuration halting problem is undecidable, and a computable map sends each
configuration to a word that dies in the coded group exactly when the
configuration halts, then the uniform word problem on codes is undecidable.

The computability of `w` is not removable: composing a computable predicate with
an arbitrary map need not be computable, which is precisely why the indexed form
of the source theorem was not enough. -/
theorem not_computablePred_wordProblemPred_of_word_map
    {mm : ModularMachine} {c : PresentationCodes.PresentationCode}
    (hmm : ¬ ComputablePred fun p : ℕ × ℕ => mm.Halts p)
    {w : ℕ × ℕ → List (ℕ × Bool)} (hw : Computable w)
    (hagree : ∀ p : ℕ × ℕ, WordProblem c (w p) ↔ mm.Halts p) :
    ¬ ComputablePred wordProblemPred := by
  intro hcomp
  refine hmm ?_
  have hmap : Computable fun p : ℕ × ℕ => (c, w p) :=
    (Computable.const c).pair hw
  have hcomp2 : ComputablePred fun p : ℕ × ℕ => wordProblemPred (c, w p) :=
    MarkovMFConsequences.computablePred_comp hcomp hmap
  exact hcomp2.of_eq fun p => hagree p

/-- **`D4'`, reduced to the word map.**  Supplying a computable
configuration-to-word map for the Boone group of an arbitrary machine, in
`finalGroupCode`'s numbering, discharges the uniform word problem's
undecidability.

The machine is obtained from the configuration-form source theorem, and `hM` is
derivable for any modular machine from `size_pos`, so the hypothesis is quantified
over exactly the data the group side produces. -/
theorem not_computablePred_wordProblemPred_of_boone_words
    (H : ∀ (mm : ModularMachine) (hM : (mm.size : ℤ) ≠ 0),
      ∃ w : ℕ × ℕ → List (ℕ × Bool), Computable w ∧
        ∀ p : ℕ × ℕ, WordProblem (finalGroupCode mm hM) (w p) ↔ mm.Halts p) :
    ¬ ComputablePred wordProblemPred := by
  obtain ⟨mm, hmm⟩ := exists_modularMachine_config_halting_not_computablePred
  have hM : (mm.size : ℤ) ≠ 0 := by
    have h := mm.size_pos
    exact_mod_cast h.ne'
  obtain ⟨w, hw, hagree⟩ := H mm hM
  exact not_computablePred_wordProblemPred_of_word_map hmm hw hagree

end Computability
end GroupApproximation
