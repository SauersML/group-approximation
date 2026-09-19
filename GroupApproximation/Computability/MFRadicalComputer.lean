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

/-! ## A fixed universal Boone controller -/

/-- The universal modular-machine package retained from the machine compiler.
Its second component is a computable map from partial-recursive program
numbers to configurations, and the last component is the exact evaluation
specification. -/
private theorem exists_controlPackage :
    ∃ (mm : ModularMachine) (f : ℕ → ℕ × ℕ), Computable f ∧
      ∀ m : ℕ, mm.Halts (f m) ↔
        (Nat.Partrec.Code.eval
          (Denumerable.ofNat Nat.Partrec.Code m) 0).Dom :=
  Computability.exists_modularMachine_universal_control 0

/-- One fixed modular machine which runs the numeral-indexed universal partial
recursive function. -/
def controlMachine : ModularMachine := exists_controlPackage.choose

/-- The computable initial configuration for program number `m`. -/
def controlIndex (m : ℕ) : ℕ × ℕ :=
  exists_controlPackage.choose_spec.choose m

/-- The universal controller's input map is computable. -/
theorem computable_controlIndex : Computable controlIndex :=
  exists_controlPackage.choose_spec.choose_spec.1

/-- Exact universal semantics of the fixed controller. -/
theorem controlMachine_halts_controlIndex_iff (m : ℕ) :
    controlMachine.Halts (controlIndex m) ↔
      (Nat.Partrec.Code.eval
        (Denumerable.ofNat Nat.Partrec.Code m) 0).Dom :=
  exists_controlPackage.choose_spec.choose_spec.2 m

/-- The fixed controller really has undecidable configuration halting. -/
theorem controlMachine_halting_not_computable :
    ¬ ComputablePred fun p : ℕ × ℕ => controlMachine.Halts p :=
  fun hcomp => UniversalCode.universalPartial_halting_undecidable 0
    ((MarkovMFConsequences.computablePred_comp hcomp computable_controlIndex).of_eq
      controlMachine_halts_controlIndex_iff)

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

/-! ## The partial-recursive-code-indexed family -/

/-- The universal controller configuration attached to a partial-recursive
code. -/
def codeConfig (c : Nat.Partrec.Code) : ℕ × ℕ :=
  controlIndex (Encodable.encode c)

/-- The code-to-configuration map is computable. -/
theorem computable_codeConfig : Computable codeConfig :=
  computable_controlIndex.comp Computable.encode

/-- The explicit raw Boone word attached to a partial-recursive code. -/
def codeRawWord (c : Nat.Partrec.Code) : List (ℕ × Bool) :=
  controlRawWord (codeConfig c)

/-- The raw word family used by the Gödel construction is computable. -/
theorem computable_codeRawWord : Computable codeRawWord :=
  computable_controlRawWord.comp computable_codeConfig

/-- The MF-radical word attached to a partial-recursive code. -/
def codeWord (c : Nat.Partrec.Code) : Carrier := word (codeConfig c)

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

/-- Exact universal semantics of the code-indexed radical word: it is trivial
precisely when the represented partial-recursive program halts on input zero. -/
theorem codeWord_eq_one_iff_eval_dom (c : Nat.Partrec.Code) :
    codeWord c = 1 ↔ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [codeWord, word_eq_one_iff_halts]
  change controlMachine.Halts (controlIndex (Encodable.encode c)) ↔ _
  rw [controlMachine_halts_controlIndex_iff]
  simp

/-- Every program-indexed word remains in the MF residual. -/
theorem codeWord_normMFInvisible (c : Nat.Partrec.Code) :
    NormMFInvisible (codeWord c) := word_normMFInvisible (codeConfig c)

/-- Every program-indexed word lies in the derived layer of the MF residual. -/
theorem codeWord_mem_commutator_residual (c : Nat.Partrec.Code) :
    codeWord c ∈ ⁅normMFResidual Carrier, (⊤ : Subgroup Carrier)⁆ :=
  word_mem_commutator_residual (codeConfig c)

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
      Computable controlRawWord ∧
      (∀ p, NormMFInvisible (word p)) ∧
      (∀ p, word p ∈ ⁅normMFResidual Carrier,
        (⊤ : Subgroup Carrier)⁆) ∧
      (∀ p, word p = 1 ↔ controlMachine.Halts p) ∧
      ¬ ComputablePred fun p : ℕ × ℕ => word p = 1 :=
  ⟨carrier_isFinitelyPresented, carrier_not_isOperatorMF,
    computable_controlRawWord, word_normMFInvisible,
    word_mem_commutator_residual, word_eq_one_iff_halts,
    promised_word_problem_not_computable⟩

/-- Closed code-indexed form used by the incompleteness theorem: program codes
are sent computably to explicit Boone words, and the corresponding words in
the one fixed carrier have the exact universal halting truth table while
remaining in the derived layer of the MF residual. -/
theorem code_closed_package :
    Group.IsFinitelyPresented Carrier ∧
      ¬ IsOperatorMF Carrier ∧
      Computable codeRawWord ∧
      (∀ c : Nat.Partrec.Code, NormMFInvisible (codeWord c)) ∧
      (∀ c : Nat.Partrec.Code,
        codeWord c ∈ ⁅normMFResidual Carrier, (⊤ : Subgroup Carrier)⁆) ∧
      (∀ c : Nat.Partrec.Code,
        codeWord c = 1 ↔ (Nat.Partrec.Code.eval c 0).Dom) :=
  ⟨carrier_isFinitelyPresented, carrier_not_isOperatorMF,
    computable_codeRawWord, codeWord_normMFInvisible,
    codeWord_mem_commutator_residual, codeWord_eq_one_iff_eval_dom⟩

end

end MFRadicalComputer
end GroupApproximation
