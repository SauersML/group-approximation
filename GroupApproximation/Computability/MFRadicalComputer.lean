import GroupApproximation.Algebra.FaithfulRadicalCocycle
import GroupApproximation.Computability.BooneGroupCode
import GroupApproximation.Computability.BooneWordProblemUndecidable
import GroupApproximation.Computability.ModularMachineConfigHalting
import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.OperatorMFFreeProductConsequences

/-!
# One fixed finitely presented computer inside the MF residual

The literal non-MF endpoint supplies a nonidentity `NormMFInvisible` mark.
A fixed Boone group supplies a computable family of elements which are trivial
exactly on the halting configurations of one machine with undecidable
configuration-halting problem.  Their free product is fixed and finitely
presented.  The faithful commutator gate turns each Boone element into an
MF-invisible word without changing its identity truth value.

Every theorem in this file is closed: the modular machine is chosen from the
repository's premise-free computability theorem and the analytic seed is the
literal premise-free MF endpoint.  No literature statement is a parameter.
-/

namespace GroupApproximation
namespace MFRadicalComputer

open BooneGroup BooneTowerPresentation BooneWords
open Computability AdianRabinWordProblem PresentationCodes
open FaithfulRadicalCocycle LiteralNonMFEndpoint
open LiteralNonMFLinearWitness LiteralNonMFPresentation
open scoped commutatorElement Monoid.Coprod

noncomputable section

/-! ## A fixed Boone controller -/

/-- One fixed modular machine whose configuration-halting predicate is not
computable. -/
def controlMachine : ModularMachine :=
  Classical.choose
    Computability.exists_modularMachine_config_halting_not_computablePred

/-- The fixed controller really has undecidable configuration halting. -/
theorem controlMachine_halting_not_computable :
    ¬ ComputablePred fun p : ℕ × ℕ => controlMachine.Halts p :=
  Classical.choose_spec
    Computability.exists_modularMachine_config_halting_not_computablePred

theorem controlMachine_size_ne_zero :
    (controlMachine.size : ℤ) ≠ 0 := by
  exact_mod_cast controlMachine.size_pos.ne'

/-- The single finite presentation used as the computational control factor. -/
abbrev ControlGroup : Type :=
  PresentationCodes.Carrier
    (finalGroupCode controlMachine controlMachine_size_ne_zero)

/-- The explicit raw Boone word for a configuration. -/
def controlRawWord (p : ℕ × ℕ) : List (ℕ × Bool) :=
  rawComm (machineTowerPres controlMachine controlMachine_size_ne_zero) p

theorem computable_controlRawWord : Computable controlRawWord :=
  computable_rawComm
    (machineTowerPres controlMachine controlMachine_size_ne_zero)

/-- The element of the fixed Boone group named by `controlRawWord`. -/
def controlElement (p : ℕ × ℕ) : ControlGroup :=
  PresentedGroup.mk
    (relatorSet (finalGroupCode controlMachine controlMachine_size_ne_zero))
    (wordOf (finalGroupCode controlMachine controlMachine_size_ne_zero)
      (controlRawWord p))

/-- Exact correctness of the fixed Boone controller. -/
theorem controlElement_eq_one_iff_halts (p : ℕ × ℕ) :
    controlElement p = 1 ↔ controlMachine.Halts p := by
  change WordProblem
      (finalGroupCode controlMachine controlMachine_size_ne_zero)
      (controlRawWord p) ↔ controlMachine.Halts p
  exact
    (wordProblem_rawComm_iff
      (machineTowerPres controlMachine controlMachine_size_ne_zero) p).trans
      (commElt_eq_one_iff_halts controlMachine controlMachine_size_ne_zero p)

/-! ## The fixed MF-radical computer -/

/-- One fixed finitely presented carrier containing the literal MF seed and
the fixed Boone controller as free factors. -/
abbrev Carrier : Type := MarkedGroup ∗ ControlGroup

/-- The radical-valued output word for configuration `p`. -/
def word (p : ℕ × ℕ) : Carrier :=
  gate mark (controlElement p)

/-- Every output word lies in the operator-MF residual. -/
theorem word_normMFInvisible (p : ℕ × ℕ) :
    NormMFInvisible (word p) := by
  intro I U X rho
  have hseed :
      rho (Monoid.Coprod.inl mark : Carrier) = 1 :=
    (literal_mark_normMFInvisible.map
      (Monoid.Coprod.inl : MarkedGroup →* Carrier)) I U X rho
  simp [word, gate, map_commutatorElement, hseed]

/-- Every output lies in the derived layer `[Res_MF, Carrier]`. -/
theorem word_mem_commutator_residual (p : ℕ × ℕ) :
    word p ∈ ⁅normMFResidual Carrier, (⊤ : Subgroup Carrier)⁆ := by
  apply gate_mem_commutator
  exact literal_mark_normMFInvisible.map
    (Monoid.Coprod.inl : MarkedGroup →* Carrier)

/-- The radical gate has exactly the controller's truth table. -/
theorem word_eq_one_iff_halts (p : ℕ × ℕ) :
    word p = 1 ↔ controlMachine.Halts p := by
  rw [word, gate_eq_one_iff literal_mark_ne_one,
    controlElement_eq_one_iff_halts]

/-- Nonhalting is exactly nontrivial MF-invisibility. -/
theorem nonhalt_iff_nontrivial_invisible (p : ℕ × ℕ) :
    ¬ controlMachine.Halts p ↔
      word p ≠ 1 ∧ NormMFInvisible (word p) := by
  constructor
  · intro hnonhalt
    exact ⟨fun hone ↦ hnonhalt ((word_eq_one_iff_halts p).mp hone),
      word_normMFInvisible p⟩
  · rintro ⟨hne, _⟩ hhalts
    exact hne ((word_eq_one_iff_halts p).mpr hhalts)

/-- The carrier is one fixed finitely presented group. -/
theorem carrier_isFinitelyPresented : Group.IsFinitelyPresented Carrier := by
  infer_instance

/-- The carrier is non-MF because its literal left factor is non-MF. -/
theorem carrier_not_isOperatorMF : ¬ IsOperatorMF Carrier :=
  not_isOperatorMF_coprod_left literal_not_isOperatorMF

/-- Identity testing remains undecidable on the computable family whose every
member is promised to lie in the MF residual. -/
theorem promised_word_problem_not_computable :
    ¬ ComputablePred fun p : ℕ × ℕ => word p = 1 := by
  intro h
  exact controlMachine_halting_not_computable
    (h.of_eq fun p => word_eq_one_iff_halts p)

/-- Closed endpoint package for the single finitely presented MF-radical
computer. -/
theorem closed_package :
    Group.IsFinitelyPresented Carrier ∧
      ¬ IsOperatorMF Carrier ∧
      (∀ p, NormMFInvisible (word p)) ∧
      (∀ p, word p = 1 ↔ controlMachine.Halts p) ∧
      ¬ ComputablePred fun p : ℕ × ℕ => word p = 1 :=
  ⟨carrier_isFinitelyPresented, carrier_not_isOperatorMF,
    word_normMFInvisible, word_eq_one_iff_halts,
    promised_word_problem_not_computable⟩

end

end MFRadicalComputer
end GroupApproximation
