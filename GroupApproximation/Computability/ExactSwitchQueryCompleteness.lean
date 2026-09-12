import GroupApproximation.Computability.CodeDovetailStageEvents
import GroupApproximation.Computability.ExactLiteralSwitchQuery

/-!
# Exact second-level completeness of the code-indexed non-MF switch

This is the unconditional endpoint available before any finite-presentation
compiler is invoked.  A partial-recursive program code is sent, by a uniform
primitive-recursive dovetail, to the countable event-ray presentation.  The
fixed literal marked query is then exactly `INF`/`FIN`:

* every source homomorphism kills the mark exactly when the program domain is
  infinite;
* some source homomorphism preserves the mark exactly when the program domain
  is finite;
* every target in the surviving branch is non-MF.

Thus the first predicate is `Π⁰₂`-complete and the second is
`Σ⁰₂`-complete.  This file deliberately makes no finite-presentation claim.
-/

namespace GroupApproximation
namespace ExactSwitchQueryCompleteness

open Nat.Partrec
open ArithmeticalHierarchy
open SecondLevelIndexSets
open CodeDovetailStageEvents
open ExactLiteralEFinInfSwitch
open ExactLiteralSwitchQuery

noncomputable section

/-- The target group uniformly interpreted from a partial-recursive code. -/
abbrev SwitchTarget (c : Code) : Type :=
  SwitchGroup (codeStageEvents c)

/-- The universal fixed-mark query on the code-indexed switch target. -/
def SwitchKills (c : Code) : Prop :=
  Kills (SwitchTarget c)

/-- The existential fixed-mark query on the code-indexed switch target. -/
def SwitchSurvives (c : Code) : Prop :=
  Survives (SwitchTarget c)

/-- Exact `INF` semantics of the universal query. -/
theorem switchKills_iff_infiniteDomain (c : Code) :
    SwitchKills c ↔ InfiniteDomain c := by
  constructor
  · intro hkill
    by_contra hinfinite
    have hfinite : FiniteDomain c := by
      simpa only [InfiniteDomain, FiniteDomain, Set.not_infinite] using hinfinite
    have hsurvive : SwitchSurvives c :=
      survives_of_finiteEvents _ (finiteDomain_finiteEvents c hfinite)
    exact (survives_iff_not_kills (SwitchTarget c)).mp hsurvive hkill
  · intro hinfinite
    exact kills_of_infiniteEvents _ (infiniteDomain_infiniteEvents c hinfinite)

/-- Exact `FIN` semantics of the existential query. -/
theorem switchSurvives_iff_finiteDomain (c : Code) :
    SwitchSurvives c ↔ FiniteDomain c := by
  constructor
  · intro hsurvive
    by_contra hfinite
    have hinfinite : InfiniteDomain c := hfinite
    have hkill : SwitchKills c :=
      kills_of_infiniteEvents _ (infiniteDomain_infiniteEvents c hinfinite)
    exact (survives_iff_not_kills (SwitchTarget c)).mp hsurvive hkill
  · intro hfinite
    exact survives_of_finiteEvents _ (finiteDomain_finiteEvents c hfinite)

/-- The universal switch query lies in `Π⁰₂`. -/
theorem switchKills_pi02 : Pi02 SwitchKills := by
  refine (pi02_congr fun c => ?_).2 infiniteDomain_pi02
  exact switchKills_iff_infiniteDomain c

/-- The universal switch query is `Π⁰₂`-hard under computable many-one
reductions. -/
theorem switchKills_pi02Hard : Pi02Hard SwitchKills := by
  intro p hp
  obtain ⟨f, hf, hcorrect⟩ := infiniteDomain_pi02Hard p hp
  exact ⟨f, hf, fun a => (hcorrect a).trans
    (switchKills_iff_infiniteDomain (f a)).symm⟩

/-- The universal fixed-mark query on the exact switch is `Π⁰₂`-complete. -/
theorem switchKills_pi02Complete : Pi02Complete SwitchKills :=
  ⟨switchKills_pi02, switchKills_pi02Hard⟩

/-- The existential switch query lies in `Σ⁰₂`. -/
theorem switchSurvives_sigma02 : Sigma02 SwitchSurvives := by
  refine (sigma02_congr fun c => ?_).2 finiteDomain_sigma02
  exact switchSurvives_iff_finiteDomain c

/-- The existential switch query is `Σ⁰₂`-hard. -/
theorem switchSurvives_sigma02Hard : Sigma02Hard SwitchSurvives := by
  intro p hp
  obtain ⟨f, hf, hcorrect⟩ := finiteDomain_sigma02Hard p hp
  exact ⟨f, hf, fun a => (hcorrect a).trans
    (switchSurvives_iff_finiteDomain (f a)).symm⟩

/-- The existential fixed-mark query on the exact switch is
`Σ⁰₂`-complete. -/
theorem switchSurvives_sigma02Complete : Sigma02Complete SwitchSurvives :=
  ⟨switchSurvives_sigma02, switchSurvives_sigma02Hard⟩

/-- Every positive instance of the existential query is a non-MF target. -/
theorem surviving_switch_not_isWeakMF (c : Code) (h : SwitchSurvives c) :
    ¬ IsWeakMF (SwitchTarget c) :=
  not_isWeakMF_of_survives h

/-- The complete truth table together with the non-MF consequence. -/
theorem exact_second_level_nonMF_switch (c : Code) :
    (SwitchKills c ↔ InfiniteDomain c) ∧
      (SwitchSurvives c ↔ FiniteDomain c) ∧
      (SwitchSurvives c → ¬ IsWeakMF (SwitchTarget c)) :=
  ⟨switchKills_iff_infiniteDomain c,
    switchSurvives_iff_finiteDomain c,
    surviving_switch_not_isWeakMF c⟩

end

end ExactSwitchQueryCompleteness
end GroupApproximation
