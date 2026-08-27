import GroupApproximation.Computability.ParametricRecursiveSwitchPresentation
import GroupApproximation.Computability.PresentationCodeCompleteness

/-!
# The finite-presentation seed and the FIN/INF switch

The recognition construction only needs a fixed finitely presented non-MF
group.  The seed used here is the repository's closed negative presentation
code `PresentationCodes.negativeCode`, which presents the companion paper's
finitely presented non-MF group and is non-MF with no hypothesis
(`not_isOperatorMF_negativeCode`, the badge of `lem:seed`).  The printed
proof of `lem:seed` takes the group of Theorem C instead.  That reading is
`SeedRemarkTheoremC`, which is a separate module: the two codes are
interchangeable for everything below, which uses only that the seed is
finitely presented and not MF, so nothing here imports `SeedFromTheoremC`
and the recognition chain does not build through Theorem C's recorded
debts.  Once those debts are discharged, `seedCode` may be repointed to
`seedCodeC` by changing one line.  The seed is fed to the executable
parametric finite-seed switch.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Switch

open Nat.Partrec PresentationCodes SecondLevelIndexSets
open ParametricRecursiveSwitchPresentation

noncomputable section

/-- **The fixed finitely presented non-MF seed** (`lem:seed`): the closed
negative presentation code, non-MF with no hypothesis. -/
abbrev seedCode : PresentationCode := PresentationCodes.negativeCode

/-- The group carried by the seed presentation. -/
abbrev H : Type := Carrier seedCode

instance : Group H := inferInstance
instance : Countable H := inferInstance
instance : Group.IsFinitelyPresented H := inferInstance

/-- **`lem:seed`**: the seed is not MF. -/
theorem seed_not_isOperatorMF : ¬ IsOperatorMF H :=
  PresentationCodes.not_isOperatorMF_negativeCode

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
