import GroupApproximation.Computability.ParametricRecursiveSwitchPresentation
import GroupApproximation.Computability.PresentationCodeCompleteness
import GroupApproximation.Manuscript.MFRecognition.SeedFromTheoremC

/-!
# The finite-presentation seed and the FIN/INF switch

The recognition construction only needs a fixed finitely presented non-MF
group: the paper's `E`, the group of Theorem C, coded in
`SeedFromTheoremC` (`lem:seed`).  It is fed to the executable parametric
finite-seed switch.  This avoids an irrelevant Diamond-Lemma word-problem
detour through the particular Leavitt group used in the companion paper.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Switch

open Nat.Partrec PresentationCodes SecondLevelIndexSets
open ParametricRecursiveSwitchPresentation

noncomputable section

/-- **The fixed finitely presented non-MF seed: the paper's `E`**, the group of
Theorem C, coded by `SeedFromTheoremC.seedCodeC` (`lem:seed`). -/
abbrev seedCode : PresentationCode := SeedFromTheoremC.seedCodeC

/-- The group carried by the seed presentation. -/
abbrev H : Type := Carrier seedCode

instance : Group H := inferInstance
instance : Countable H := inferInstance
instance : Group.IsFinitelyPresented H := inferInstance

/-- **`lem:seed`**: the seed is not MF. -/
theorem seed_not_isOperatorMF : ¬ IsOperatorMF H :=
  SeedFromTheoremC.not_isOperatorMF_seedCodeC

/-- The recursive presentation emitted for program `e`. -/
abbrev switchCode (e : Code) : Code :=
  parametricSwitchEnumeratorCode seedCode e

/-- Its presented group. -/
abbrev SwitchGroup (e : Code) : Type := ParametricCompiledCarrier seedCode e

/-- The switch compiler is computable uniformly in the program index. -/
theorem switchCode_computable : Computable switchCode :=
  computable₂_parametricSwitchEnumeratorCode.comp
    (Computable.const seedCode) Computable.id

/-- The INF branch is trivial. -/
theorem switchGroup_subsingleton_of_infiniteDomain (e : Code)
    (he : InfiniteDomain e) : Subsingleton (SwitchGroup e) :=
  compiledCarrier_subsingleton_of_infiniteDomain seedCode e he

/-- The INF branch is explicitly the trivial group. -/
theorem switchGroup_equiv_punit_of_infiniteDomain (e : Code)
    (he : InfiniteDomain e) : Nonempty (MulEquiv (SwitchGroup e) PUnit) :=
  compiledCarrier_equiv_punit_of_infiniteDomain seedCode e he

/-- The FIN branch is exactly the fixed non-MF seed. -/
theorem switchGroup_equiv_seed_of_finiteDomain (e : Code)
    (he : FiniteDomain e) : Nonempty (MulEquiv (SwitchGroup e) H) :=
  compiledCarrier_equiv_seed_of_finiteDomain seedCode e he

/-- In particular, the non-MF seed embeds in every FIN-branch group. -/
theorem seed_embeds_switchGroup_of_finiteDomain (e : Code)
    (he : FiniteDomain e) :
    ∃ f : H →* SwitchGroup e, Function.Injective f := by
  obtain ⟨equiv⟩ := switchGroup_equiv_seed_of_finiteDomain e he
  exact ⟨equiv.symm.toMonoidHom, equiv.symm.injective⟩

end

end Switch
end MFRecognition
end Manuscript
end GroupApproximation
