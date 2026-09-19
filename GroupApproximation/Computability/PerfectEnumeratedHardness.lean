import GroupApproximation.Computability.IsoInvariantSwitchHardness
import GroupApproximation.Computability.BooneGroupFreeBasis
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Perfectness is second-level hard on enumerated presentations

Perfectness — every element lies in the commutator subgroup — is
isomorphism invariant, holds for the trivial group and fails for `Z`, so
the isomorphism-invariant switch of
`Computability.IsoInvariantSwitchHardness` makes it `Π⁰₂`-hard on
enumerated presentation codes and its failure `Σ⁰₂`-hard.  Research node
`perfectness-and-bounded-solvability-are-pi2-complete`.
-/

namespace GroupApproximation
namespace PerfectEnumeratedHardness

open ArithmeticalHierarchy IsoInvariantSwitchHardness

/-- Perfectness: every element is in the commutator subgroup. -/
def IsPerfectGroup (H : Type) [Group H] : Prop := ∀ x : H, x ∈ commutator H

theorem isPerfect_punit : IsPerfectGroup PUnit := by
  intro x
  have hx : x = 1 := Subsingleton.elim _ _
  rw [hx]
  exact one_mem _

theorem isPerfect_of_mulEquiv {H K : Type} [Group H] [Group K] (e : H ≃* K)
    (hK : IsPerfectGroup K) : IsPerfectGroup H := by
  intro x
  have hmap : (commutator K).map e.symm.toMonoidHom ≤ commutator H := by
    rw [commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hmem : e.symm (e x) ∈ (commutator K).map e.symm.toMonoidHom :=
    Subgroup.mem_map_of_mem _ (hK (e x))
  have := hmap hmem
  simpa using this

/-- The infinite cyclic group is not perfect: it maps onto an infinite
commutative group. -/
theorem not_isPerfect_freeGroup_one : ¬ IsPerfectGroup (FreeGroup (Fin 1)) := by
  intro h
  set φ : FreeGroup (Fin 1) →* Multiplicative ℤ :=
    FreeGroup.lift fun _ ↦ Multiplicative.ofAdd (1 : ℤ) with hφ
  have hker : commutator (FreeGroup (Fin 1)) ≤ φ.ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun a _ b _ ↦ ?_
    simp [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_inv]
  have hx : φ (FreeGroup.of (0 : Fin 1)) = 1 := hker (h (FreeGroup.of (0 : Fin 1)))
  have hval : φ (FreeGroup.of (0 : Fin 1)) = Multiplicative.ofAdd (1 : ℤ) := by
    simp [hφ]
  rw [hval] at hx
  exact absurd (congrArg Multiplicative.toAdd hx) (by decide)

/-- **Perfectness of enumerated presentation codes is `Π⁰₂`-hard.** -/
theorem perfectCode_pi02Hard :
    Pi02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
      IsPerfectGroup (EnumeratedPresentationCodes.Carrier q)) := by
  obtain ⟨seed, ⟨e⟩⟩ := PresentationCodes.exists_code_mulEquiv (FreeGroup (Fin 1))
  exact enumeratedCodeProperty_pi02Hard
    (P := fun (H : Type) (_ : Group H) ↦ IsPerfectGroup H)
    { invariant := fun e h ↦ isPerfect_of_mulEquiv e h
      trivial := isPerfect_punit
      forbidden := seed
      forbidden_not := fun h ↦ not_isPerfect_freeGroup_one (isPerfect_of_mulEquiv e.symm h) }

/-- **Failure of perfectness is `Σ⁰₂`-hard.** -/
theorem notPerfectCode_sigma02Hard :
    Sigma02Hard (fun q : EnumeratedPresentationCodes.PresentationCode ↦
      ¬ IsPerfectGroup (EnumeratedPresentationCodes.Carrier q)) :=
  pi02Hard_compl perfectCode_pi02Hard

end PerfectEnumeratedHardness
end GroupApproximation
