import GroupApproximation.Computability.ExactSwitchQueryCompleteness
import GroupApproximation.Computability.WordProblemRE
import Mathlib.Computability.Halting

/-!
# Algorithmic consequences of the exact fixed-mark switch

The exact event-ray switch has only two semantic branches.  An infinite event
set gives the trivial, hence weak-MF, group.  A finite event set leaves the
literal non-MF group, and its fixed MF-invisible mark survives.  Consequently
weak-MF and non-MF recognition on this one uniformly code-indexed family are
respectively `Pi02`-complete and `Sigma02`-complete.

The second half records strict first-level consequences without invoking an
arithmetical-hierarchy separation as an external input.  A numerical copy of
nonhalting belongs to both second-level classes but is not recursively
enumerable.  Completeness therefore shows that neither branch of the switch is
RE or coRE.  In particular neither side has a sound and complete finite,
computably checkable certificate system.
-/

namespace GroupApproximation
namespace ExactSwitchAlgorithmicConsequences

open Nat.Partrec
open ArithmeticalHierarchy
open ExactLiteralEFinInfSwitch
open ExactLiteralSwitchQuery
open ExactSwitchQueryCompleteness

noncomputable section

/-! ## The fixed switch recognizes weak-MF exactly -/

/-- Actual weak-MF recognition restricted to the exact event-ray family. -/
def SwitchWeakMF (c : Code) : Prop :=
  IsWeakMF (SwitchTarget c)

/-- Actual non-MF recognition restricted to the exact event-ray family. -/
def SwitchNonMF (c : Code) : Prop :=
  ¬ IsWeakMF (SwitchTarget c)

theorem switchWeakMF_of_kills (c : Code) (h : SwitchKills c) :
    SwitchWeakMF c := by
  have hinfinite := (switchKills_iff_infiniteDomain c).1 h
  letI : Subsingleton (SwitchTarget c) :=
    subsingleton_of_infiniteEvents _
      (CodeDovetailStageEvents.infiniteDomain_infiniteEvents c hinfinite)
  letI : Finite (SwitchTarget c) :=
    Finite.of_injective (fun _ : SwitchTarget c => PUnit.unit)
      (fun _ _ _ => Subsingleton.elim _ _)
  exact isWeakMF_of_finite (SwitchTarget c)

theorem switchKills_of_weakMF (c : Code) (h : SwitchWeakMF c) :
    SwitchKills c := by
  by_contra hkill
  have hsurvives : SwitchSurvives c := by
    exact (survives_iff_not_kills (SwitchTarget c)).2 hkill
  exact surviving_switch_not_isWeakMF c hsurvives h

/-- On the exact family, the universal fixed-mark query is not merely an
obstruction: it is equivalent to actual weak-MF-ness. -/
theorem switchKills_iff_weakMF (c : Code) :
    SwitchKills c ↔ SwitchWeakMF c :=
  ⟨switchWeakMF_of_kills c, switchKills_of_weakMF c⟩

/-- On the exact family, survival of the one fixed MF-invisible mark is
equivalent to actual non-MF-ness. -/
theorem switchSurvives_iff_nonMF (c : Code) :
    SwitchSurvives c ↔ SwitchNonMF c := by
  change SwitchSurvives c ↔ ¬ SwitchWeakMF c
  exact (survives_iff_not_kills (SwitchTarget c)).trans
    (not_congr (switchKills_iff_weakMF c))

/-- Weak-MF recognition is `Pi02`-complete even on the exact event-ray
family. -/
theorem switchWeakMF_pi02Complete : Pi02Complete SwitchWeakMF := by
  constructor
  · exact (pi02_congr fun c => switchKills_iff_weakMF c).1
      switchKills_pi02
  · intro p hp
    obtain ⟨f, hf, hcorrect⟩ := switchKills_pi02Hard p hp
    exact ⟨f, hf, fun n => (hcorrect n).trans (switchKills_iff_weakMF (f n))⟩

/-- Non-MF recognition is `Sigma02`-complete even on the exact event-ray
family; every positive instance is witnessed by survival of the same literal
MF-invisible mark. -/
theorem switchNonMF_sigma02Complete : Sigma02Complete SwitchNonMF := by
  constructor
  · exact (sigma02_congr fun c => switchSurvives_iff_nonMF c).1
      switchSurvives_sigma02
  · intro p hp
    obtain ⟨f, hf, hcorrect⟩ := switchSurvives_sigma02Hard p hp
    exact ⟨f, hf, fun n =>
      (hcorrect n).trans (switchSurvives_iff_nonMF (f n))⟩

/-! ## An internal strictness witness -/

/-- A numerical presentation of nonhalting, used only as an unconditional
strictness witness. -/
def NonhaltsZero (n : ℕ) : Prop :=
  ¬ (Code.eval (Denumerable.ofNat Code n) 0).Dom

/-- The bounded test that the decoded program has not halted by stage `s`. -/
def stillRunningCheck (z : ℕ × ℕ) : Bool :=
  !(Code.evaln z.2 (Denumerable.ofNat Code z.1) 0).isSome

theorem primrec_stillRunningCheck : Primrec stillRunningCheck := by
  have hcode : Primrec fun z : ℕ × ℕ => Denumerable.ofNat Code z.1 :=
    (Primrec.ofNat Code).comp Primrec.fst
  have hstage : Primrec fun z : ℕ × ℕ => z.2 := Primrec.snd
  have heval : Primrec fun z : ℕ × ℕ =>
      Code.evaln z.2 (Denumerable.ofNat Code z.1) 0 :=
    Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair hstage hcode) (Primrec.const 0))
  exact Primrec.not.comp (Primrec.option_isSome.comp heval)

theorem nonhaltsZero_pi02 : Pi02 NonhaltsZero := by
  have hpred : PrimrecPred fun z : ℕ × ℕ => stillRunningCheck z = true :=
    Primrec.eq.comp primrec_stillRunningCheck (Primrec.const true)
  refine ⟨fun z => stillRunningCheck z = true,
    hpred.computablePred.to_re, ?_⟩
  intro n
  constructor
  · intro hnonhalt stage
    cases hs : (Code.evaln stage (Denumerable.ofNat Code n) 0).isSome with
    | false => simp [stillRunningCheck, hs]
    | true =>
        exfalso
        apply hnonhalt
        exact (SecondLevelIndexSets.eval_dom_iff_exists_evaln_isSome
          (Denumerable.ofNat Code n) 0).2 ⟨stage, hs⟩
  · intro hall hhalt
    obtain ⟨stage, hs⟩ :=
      (SecondLevelIndexSets.eval_dom_iff_exists_evaln_isSome
        (Denumerable.ofNat Code n) 0).1 hhalt
    have hstill := hall stage
    simp [stillRunningCheck, hs] at hstill

theorem nonhaltsZero_sigma02 : Sigma02 NonhaltsZero := by
  unfold Sigma02
  have heval : Partrec fun z : ℕ × ℕ =>
      Code.eval (Denumerable.ofNat Code z.1) 0 :=
    Code.eval_part.comp
      ((Computable.ofNat Code).comp Computable.fst) (Computable.const 0)
  refine ⟨fun z => (Code.eval (Denumerable.ofNat Code z.1) 0).Dom,
    heval.dom_re, ?_⟩
  intro n
  classical
  simp [NonhaltsZero]

theorem nonhaltsZero_not_re : ¬ REPred NonhaltsZero := by
  intro hre
  apply ComputablePred.halting_problem_not_re 0
  have hpullback : REPred fun c : Code => NonhaltsZero (Encodable.encode c) :=
    MarkovMFConsequences.rePred_comp hre
      (Computable.encode : Computable fun c : Code => Encodable.encode c)
  exact hpullback.of_eq fun c => by
    simp [NonhaltsZero]

theorem not_re_of_manyOneReduction
    {B : Type*} [Primcodable B] {p : ℕ → Prop} {q : B → Prop}
    (hp : ¬ REPred p) (h : p ≤₀ q) :
    ¬ REPred q := by
  intro hq
  obtain ⟨f, hf, hcorrect⟩ := h
  have hpullback : REPred fun n => q (f n) := hq.comp hf
  exact hp (hpullback.of_eq fun n => (hcorrect n).symm)

/-! ## Neither side is RE or coRE -/

theorem switchKills_not_re : ¬ REPred SwitchKills := by
  exact not_re_of_manyOneReduction nonhaltsZero_not_re
    (switchKills_pi02Hard NonhaltsZero nonhaltsZero_pi02)

theorem switchSurvives_not_re : ¬ REPred SwitchSurvives := by
  exact not_re_of_manyOneReduction nonhaltsZero_not_re
    (switchSurvives_sigma02Hard NonhaltsZero nonhaltsZero_sigma02)

theorem switchKills_not_core : ¬ Pi01 SwitchKills := by
  intro hcore
  exact switchSurvives_not_re
    (hcore.of_eq fun c =>
      (survives_iff_not_kills (SwitchTarget c)).symm)

theorem switchSurvives_not_core : ¬ Pi01 SwitchSurvives := by
  intro hcore
  exact switchKills_not_re
    (hcore.of_eq fun c => by
      change (¬ Survives (SwitchTarget c)) ↔ Kills (SwitchTarget c)
      rw [survives_iff_not_kills]
      tauto)

theorem switchWeakMF_not_re : ¬ REPred SwitchWeakMF := by
  intro hre
  exact switchKills_not_re
    (hre.of_eq fun c => (switchKills_iff_weakMF c).symm)

theorem switchNonMF_not_re : ¬ REPred SwitchNonMF := by
  intro hre
  exact switchSurvives_not_re
    (hre.of_eq fun c => (switchSurvives_iff_nonMF c).symm)

theorem switchWeakMF_not_core : ¬ Pi01 SwitchWeakMF := by
  intro hcore
  exact switchNonMF_not_re
    (hcore.of_eq fun c => by
      change (¬ IsWeakMF (SwitchTarget c)) ↔ ¬ IsWeakMF (SwitchTarget c)
      rfl)

theorem switchNonMF_not_core : ¬ Pi01 SwitchNonMF := by
  intro hcore
  exact switchWeakMF_not_re
    (hcore.of_eq fun c => by
      change (¬ ¬ IsWeakMF (SwitchTarget c)) ↔ IsWeakMF (SwitchTarget c)
      tauto)

theorem switchWeakMF_not_computable : ¬ ComputablePred SwitchWeakMF :=
  fun h => switchWeakMF_not_re h.to_re

theorem switchNonMF_not_computable : ¬ ComputablePred SwitchNonMF :=
  fun h => switchNonMF_not_re h.to_re

/-! ## No finite checkable proof system on either side -/

theorem no_switchWeakMF_certificate_system :
    ¬ ∃ (Cert : Type) (_ : Primcodable Cert) (V : Code → Cert → Bool),
      Computable₂ V ∧
        ∀ c, (∃ π, V c π = true) ↔ SwitchWeakMF c := by
  rintro ⟨Cert, hCert, V, hV, hspec⟩
  exact switchWeakMF_not_re
    ((WordProblemRE.rePred_exists_eq_true hV).of_eq hspec)

theorem no_switchNonMF_certificate_system :
    ¬ ∃ (Cert : Type) (_ : Primcodable Cert) (V : Code → Cert → Bool),
      Computable₂ V ∧
        ∀ c, (∃ π, V c π = true) ↔ SwitchNonMF c := by
  rintro ⟨Cert, hCert, V, hV, hspec⟩
  exact switchNonMF_not_re
    ((WordProblemRE.rePred_exists_eq_true hV).of_eq hspec)

/-- Closed algorithmic endpoint for the exact fixed-mark family. -/
theorem exact_switch_algorithmic_package :
    Pi02Complete SwitchWeakMF ∧
      Sigma02Complete SwitchNonMF ∧
      (∀ c, SwitchSurvives c ↔ SwitchNonMF c) ∧
      ¬ REPred SwitchWeakMF ∧ ¬ Pi01 SwitchWeakMF ∧
      ¬ REPred SwitchNonMF ∧ ¬ Pi01 SwitchNonMF ∧
      ¬ ComputablePred SwitchWeakMF ∧
      ¬ ComputablePred SwitchNonMF :=
  ⟨switchWeakMF_pi02Complete, switchNonMF_sigma02Complete,
    switchSurvives_iff_nonMF, switchWeakMF_not_re,
    switchWeakMF_not_core, switchNonMF_not_re, switchNonMF_not_core,
    switchWeakMF_not_computable, switchNonMF_not_computable⟩

end

end ExactSwitchAlgorithmicConsequences
end GroupApproximation
