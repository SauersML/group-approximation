import GroupApproximation.Computability.IsoInvariantSwitchHardness
import GroupApproximation.Algebra.GroupTorsionFree

/-!
# Torsion-freeness is second-level hard on enumerated presentations

Power-torsion-freeness is isomorphism invariant, holds for the trivial
group, and fails for the finitely presented group `Z/2`; so the
isomorphism-invariant switch of `Computability.IsoInvariantSwitchHardness`
makes it `Π⁰₂`-hard on enumerated presentation codes and its failure
`Σ⁰₂`-hard.  The matching upper bound is paper-level: research node
`torsion-freeness-recognition-is-pi2-complete`.
-/

namespace GroupApproximation
namespace TorsionFreeEnumeratedHardness

open ArithmeticalHierarchy IsoInvariantSwitchHardness

/-- The two-element group, as a finitely presented multiplicative group. -/
abbrev TwoGroup : Type := Multiplicative (ZMod 2)

instance : Group.IsFinitelyPresented TwoGroup := by
  infer_instance

theorem not_torsionFree_two : ¬ IsPowerTorsionFree TwoGroup := by
  intro h
  have := h (Multiplicative.ofAdd (1 : ZMod 2)) 2 (by norm_num) (by decide)
  exact absurd this (by decide)

theorem torsionFree_punit : IsPowerTorsionFree PUnit := fun _ _ _ _ ↦ rfl

theorem torsionFree_of_mulEquiv {H K : Type} [Group H] [Group K] (e : H ≃* K)
    (hK : IsPowerTorsionFree K) : IsPowerTorsionFree H := by
  intro g n hn hg
  have : e g ^ n = 1 := by rw [← map_pow, hg, map_one]
  have := hK (e g) n hn this
  simpa using e.injective (by simpa using this)

/-- **Torsion-freeness of enumerated presentation codes is `Π⁰₂`-hard.** -/
theorem torsionFreeCode_pi02Hard :
    Pi02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
      IsPowerTorsionFree (EnumeratedPresentationCodes.Carrier q)) := by
  obtain ⟨seed, ⟨e⟩⟩ := PresentationCodes.exists_code_mulEquiv TwoGroup
  exact enumeratedCodeProperty_pi02Hard
    (P := fun (H : Type) (_ : Group H) ↦ IsPowerTorsionFree H)
    { invariant := fun e h ↦ torsionFree_of_mulEquiv e h
      trivial := torsionFree_punit
      forbidden := seed
      forbidden_not := fun h ↦ not_torsionFree_two (torsionFree_of_mulEquiv e.symm h) }

/-- **Having torsion is `Σ⁰₂`-hard on enumerated presentation codes.** -/
theorem hasTorsionCode_sigma02Hard :
    Sigma02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
      ¬ IsPowerTorsionFree (EnumeratedPresentationCodes.Carrier q)) :=
  pi02Hard_compl torsionFreeCode_pi02Hard

end TorsionFreeEnumeratedHardness
end GroupApproximation
