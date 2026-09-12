import GroupApproximation.Computability.IsoInvariantSwitchHardness

/-!
# Containing a free subgroup of rank two is second-level hard on enumerated presentations

"The presented group has no subgroup isomorphic to `F_2`" is isomorphism
invariant, holds for the trivial group, and fails for `F_2` itself, so the
isomorphism-invariant switch makes it `Π⁰₂`-hard on enumerated presentation
codes; equivalently, containing a nonabelian free subgroup is `Σ⁰₂`-hard.
Research node `amenability-two-generator-recursive-is-pi2-complete`
(the `CONTAINS-F2` row, `Σ⁰₂`-complete on two-generator recursive
presentations).
-/

namespace GroupApproximation
namespace FreeSubgroupEnumeratedHardness

open ArithmeticalHierarchy IsoInvariantSwitchHardness

/-- `H` contains no copy of the free group of rank two. -/
def NoFreeSubgroup (H : Type) [Group H] : Prop :=
  ∀ f : FreeGroup (Fin 2) →* H, ¬ Function.Injective f

theorem noFreeSubgroup_punit : NoFreeSubgroup PUnit := by
  intro f hf
  have h01 : FreeGroup.of (0 : Fin 2) = FreeGroup.of (1 : Fin 2) :=
    hf (Subsingleton.elim _ _)
  exact absurd (FreeGroup.of_injective h01) (by decide)

theorem noFreeSubgroup_of_mulEquiv {H K : Type} [Group H] [Group K] (e : H ≃* K)
    (hK : NoFreeSubgroup K) : NoFreeSubgroup H := by
  intro f hf
  exact hK (e.toMonoidHom.comp f) (e.injective.comp hf)

/-- **Freeness-freeness is `Π⁰₂`-hard: containing `F_2` is `Σ⁰₂`-hard on
enumerated presentation codes.** -/
theorem noFreeSubgroupCode_pi02Hard :
    Pi02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
      NoFreeSubgroup (EnumeratedPresentationCodes.Carrier q)) := by
  obtain ⟨seed, ⟨e⟩⟩ := PresentationCodes.exists_code_mulEquiv (FreeGroup (Fin 2))
  exact enumeratedCodeProperty_pi02Hard
    (P := fun (H : Type) (_ : Group H) ↦ NoFreeSubgroup H)
    { invariant := fun e h ↦ noFreeSubgroup_of_mulEquiv e h
      trivial := noFreeSubgroup_punit
      forbidden := seed
      forbidden_not := fun h ↦ h e.symm.toMonoidHom e.symm.injective }

theorem containsFreeSubgroupCode_sigma02Hard :
    Sigma02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
      ¬ NoFreeSubgroup (EnumeratedPresentationCodes.Carrier q)) :=
  pi02Hard_compl noFreeSubgroupCode_pi02Hard

end FreeSubgroupEnumeratedHardness
end GroupApproximation
