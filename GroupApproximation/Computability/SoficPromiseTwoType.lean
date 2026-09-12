import GroupApproximation.Computability.RecursiveSwitchPresentation
import GroupApproximation.Sofic.LiteralSoficAssembly
import GroupApproximation.Sofic.SoficPositiveControl
import GroupApproximation.Sofic.SoficTransfer

/-!
# A two-isomorphism-type sofic promise family

The standard enumerated-presentation compiler for the exact event switch never
leaves the class of sofic groups.  More precisely, its carrier is trivial when
the source program has infinite domain, while for finite domain it is
isomorphic to the one fixed literal group `MarkedGroup`.

The proof uses only the explicit semantic equivalence of the standard compiler,
the infinite-event collapse and finite-cut equivalence of the switch, and the
premise-free theorem `LiteralSoficAssembly.markedGroup_isSofic`.
-/

namespace GroupApproximation
namespace SoficPromiseTwoType

open Nat.Partrec
open SecondLevelIndexSets
open ExactLiteralEFinInfSwitch
open CodeDovetailStageEvents
open LiteralNonMFPresentation

noncomputable section

/-- The standard presentation carrier produced from a partial-recursive code. -/
abbrev CompiledCarrier (c : Code) : Type :=
  EnumeratedPresentationCodes.Carrier
    (RecursiveSwitchPresentation.switchEnumeratorCode c)

/-- In the infinite-domain branch, the compiled standard carrier is literally
subsingleton, hence isomorphic to the trivial group. -/
theorem compiledCarrier_subsingleton_of_infiniteDomain (c : Code)
    (hc : InfiniteDomain c) : Subsingleton (CompiledCarrier c) := by
  let e := RecursiveSwitchPresentation.standardCarrierEquivSwitch c
  letI : Subsingleton
      (SwitchGroup (codeStageEvents c)) :=
    subsingleton_of_infiniteEvents _
      (infiniteDomain_infiniteEvents c hc)
  exact ⟨fun x y => e.injective (Subsingleton.elim (e x) (e y))⟩

/-- Every element of the infinite-domain carrier is the identity. -/
theorem compiledCarrier_eq_one_of_infiniteDomain (c : Code)
    (hc : InfiniteDomain c) (x : CompiledCarrier c) : x = 1 := by
  letI : Subsingleton (CompiledCarrier c) :=
    compiledCarrier_subsingleton_of_infiniteDomain c hc
  exact Subsingleton.elim _ _

/-- The infinite-domain carrier is explicitly isomorphic to the trivial group,
not merely known abstractly to be subsingleton. -/
theorem compiledCarrier_equiv_punit_of_infiniteDomain (c : Code)
    (hc : InfiniteDomain c) :
    Nonempty (CompiledCarrier c ≃* PUnit) := by
  letI : Subsingleton (CompiledCarrier c) :=
    compiledCarrier_subsingleton_of_infiniteDomain c hc
  let f : CompiledCarrier c →* PUnit := 1
  refine ⟨MulEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro x y _
    exact Subsingleton.elim _ _
  · intro y
    exact ⟨1, Subsingleton.elim _ _⟩

/-- In the finite-domain branch, the compiled standard carrier is exactly the
fixed literal forty-one-relator group. -/
theorem compiledCarrier_equiv_markedGroup_of_finiteDomain (c : Code)
    (hc : FiniteDomain c) :
    Nonempty (CompiledCarrier c ≃* MarkedGroup) := by
  obtain ⟨e⟩ := nonempty_equiv_literal_of_finiteEvents
    (codeStageEvents c) (finiteDomain_finiteEvents c hc)
  exact ⟨(RecursiveSwitchPresentation.standardCarrierEquivSwitch c).trans e⟩

/-- Every carrier produced by the standard compiler is sofic.  In the
infinite-domain branch it is finite and trivial; in the finite-domain branch
soficity transports from the explicit literal group. -/
theorem compiled_isSofic (c : Code) : IsSofic (CompiledCarrier c) := by
  by_cases hc : InfiniteDomain c
  · letI : Subsingleton (CompiledCarrier c) :=
      compiledCarrier_subsingleton_of_infiniteDomain c hc
    letI : Finite (CompiledCarrier c) :=
      Finite.of_injective (fun _ : CompiledCarrier c => PUnit.unit)
        (fun _ _ _ => Subsingleton.elim _ _)
    exact isSofic_of_finite (CompiledCarrier c)
  · have hfinite : FiniteDomain c := by
      simpa only [FiniteDomain, InfiniteDomain, Set.not_infinite] using hc
    obtain ⟨e⟩ := compiledCarrier_equiv_markedGroup_of_finiteDomain c hfinite
    exact (isSofic_mulEquiv_iff e).mpr
      LiteralSoficAssembly.markedGroup_isSofic

/-- The complete semantic two-isomorphism-type dichotomy for the compiled
standard family. -/
theorem compiled_semantic_dichotomy (c : Code) :
    (InfiniteDomain c → Subsingleton (CompiledCarrier c)) ∧
      (FiniteDomain c → Nonempty (CompiledCarrier c ≃* MarkedGroup)) :=
  ⟨compiledCarrier_subsingleton_of_infiniteDomain c,
    compiledCarrier_equiv_markedGroup_of_finiteDomain c⟩

/-- Every compiled carrier belongs to one of exactly the two advertised
isomorphism types: the trivial group or the fixed literal group. -/
theorem compiled_two_isomorphism_types (c : Code) :
    (InfiniteDomain c ∧ Nonempty (CompiledCarrier c ≃* PUnit)) ∨
      (FiniteDomain c ∧ Nonempty (CompiledCarrier c ≃* MarkedGroup)) := by
  by_cases hc : InfiniteDomain c
  · exact Or.inl ⟨hc, compiledCarrier_equiv_punit_of_infiniteDomain c hc⟩
  · have hfinite : FiniteDomain c := by
      simpa only [FiniteDomain, InfiniteDomain, Set.not_infinite] using hc
    exact Or.inr
      ⟨hfinite, compiledCarrier_equiv_markedGroup_of_finiteDomain c hfinite⟩

end

end SoficPromiseTwoType
end GroupApproximation
