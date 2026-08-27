import GroupApproximation.Computability.HereditaryPropertySwitchCompleteness
import GroupApproximation.Kazhdan.FreeGroupSharpProfile
import GroupApproximation.Kazhdan.ShalomFinitePresentation

/-!
# Second-level hardness for isomorphism-invariant properties, and property (T)

The arbitrary-seed switch has exactly two isomorphism types, so the
hereditary hypothesis of `HereditaryPropertySwitchCompleteness` is only
ever used through group isomorphisms.  This file records the variant for
merely isomorphism-invariant properties and instantiates it at Kazhdan's
property (T): the trivial group has (T), `F_2` does not, so (T) on
enumerated presentation codes is `Π⁰₂`-hard and its failure `Σ⁰₂`-hard.
On finite presentations (T) is `Σ⁰₁`-complete and on enumerated
presentations `Σ⁰₃`-complete (research nodes
`kazhdan-property-t-of-finite-presentations-is-sigma1-complete`,
`enumerated-presentation-finite-generation-levels`); the second-level lower
bound here is the part the switch delivers directly.
-/

namespace GroupApproximation
namespace IsoInvariantSwitchHardness

open Nat.Partrec ArithmeticalHierarchy SecondLevelIndexSets PresentationCodes
open HereditaryPropertySwitchCompleteness ParametricRecursiveSwitchPresentation

/-- Switch data for an isomorphism-invariant property: invariance, the
trivial group has it, and one finite presentation code fails it. -/
structure IsoSwitchData (P : (H : Type) → [Group H] → Prop) where
  invariant : ∀ {H K : Type} [Group H] [Group K], (H ≃* K) → P K → P H
  trivial : P PUnit
  forbidden : PresentationCode
  forbidden_not : ¬ P (Carrier forbidden)

variable {P : (H : Type) → [Group H] → Prop}

/-- On the switch family the property holds iff the source has infinite domain. -/
theorem restricted_iff_infiniteDomain (D : IsoSwitchData P) (c : Code) :
    P (ParametricCompiledCarrier D.forbidden c) ↔ InfiniteDomain c := by
  constructor
  · intro hP
    by_contra hinfinite
    have hfinite : FiniteDomain c := by
      simpa only [FiniteDomain, InfiniteDomain, Set.not_infinite] using hinfinite
    obtain ⟨e⟩ := compiledCarrier_equiv_seed_of_finiteDomain D.forbidden c hfinite
    exact D.forbidden_not (D.invariant e.symm hP)
  · intro hinfinite
    obtain ⟨e⟩ := compiledCarrier_equiv_punit_of_infiniteDomain D.forbidden c hinfinite
    exact D.invariant e D.trivial

/-- Global `Π⁰₂`-hardness on enumerated presentation codes. -/
theorem enumeratedCodeProperty_pi02Hard (D : IsoSwitchData P) :
    Pi02Hard (EnumeratedCodeProperty P) := by
  intro p hp
  obtain ⟨f, hf, hcorrect⟩ := infiniteDomain_pi02Hard p hp
  refine ⟨fun n ↦ parametricSwitchEnumeratorCode D.forbidden (f n),
    (computable₂_parametricSwitchEnumeratorCode.comp
      (Computable.const D.forbidden) Computable.id).comp hf, fun n ↦ ?_⟩
  exact (hcorrect n).trans (restricted_iff_infiniteDomain D (f n)).symm

/-- The complementary `Σ⁰₂`-hardness. -/
theorem enumeratedCodeProperty_compl_sigma02Hard (D : IsoSwitchData P) :
    Sigma02Hard (fun c ↦ ¬ EnumeratedCodeProperty P c) :=
  pi02Hard_compl (enumeratedCodeProperty_pi02Hard D)

/-- **Kazhdan's property (T) on enumerated presentation codes is `Π⁰₂`-hard.** -/
theorem kazhdanCode_pi02Hard :
    Pi02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
      HasKazhdanPropertyT.{0, 0} (EnumeratedPresentationCodes.Carrier q)) := by
  obtain ⟨seed, ⟨e⟩⟩ := exists_code_mulEquiv (FreeGroup (Fin 2))
  exact enumeratedCodeProperty_pi02Hard
    { invariant := fun e h ↦ HasKazhdanPropertyT.of_mulEquiv e h
      trivial := Shalom.hasKazhdanPropertyT_of_subsingleton
      forbidden := seed
      forbidden_not := fun h ↦
        Hyperbolic.not_hasKazhdanPropertyT_freeGroup (Fin 2) ⟨0⟩
          (HasKazhdanPropertyT.of_mulEquiv e.symm h) }

/-- **Failure of property (T) on enumerated presentation codes is `Σ⁰₂`-hard.** -/
theorem nonKazhdanCode_sigma02Hard :
    Sigma02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
      ¬ HasKazhdanPropertyT.{0, 0} (EnumeratedPresentationCodes.Carrier q)) :=
  pi02Hard_compl kazhdanCode_pi02Hard

end IsoInvariantSwitchHardness
end GroupApproximation
