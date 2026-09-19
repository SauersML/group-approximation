import GroupApproximation.Computability.AbelianEnumeratedPi02
import GroupApproximation.Algebra.ProductFinitePresentation
import GroupApproximation.Meta.AxiomGuard

/-!
# A free commutator witness for the torsion-free construction

The Fournier--Facio routing argument does not require an infinite simple
torsion-free group.  It is enough to start with a finitely presented
torsion-free group whose commutator subgroup is nontrivial, saturate the normal
closure of that commutator subgroup, and protect one nonidentity commutator.

This file supplies the smallest standard choice: the free group on two
generators.  The nontriviality proof maps the two generators to noncommuting
transpositions in `S₃`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TheoremC

open scoped commutatorElement

/-- The replacement for the Hyde--Lodha factor in the saturation argument. -/
abbrev FreeCommutatorWitness : Type := FreeGroup (Fin 2)

/-- The first free generator. -/
def freeWitnessA : FreeCommutatorWitness := FreeGroup.of 0

/-- The second free generator. -/
def freeWitnessB : FreeCommutatorWitness := FreeGroup.of 1

/-- The protected element: the commutator of the two free generators. -/
def freeWitnessCommutator : FreeCommutatorWitness :=
  ⁅freeWitnessA, freeWitnessB⁆

theorem freeWitness_generators_not_commute :
    freeWitnessA * freeWitnessB ≠ freeWitnessB * freeWitnessA := by
  intro h
  let f : FreeCommutatorWitness →* Equiv.Perm (Fin 3) :=
    FreeGroup.lift fun i ↦
      if i = 0 then Equiv.swap (0 : Fin 3) 1 else Equiv.swap (1 : Fin 3) 2
  have hf := congrArg f h
  have hzero : f freeWitnessA = Equiv.swap (0 : Fin 3) 1 := by
    simp [f, freeWitnessA]
  have hone : f freeWitnessB = Equiv.swap (1 : Fin 3) 2 := by
    simp [f, freeWitnessB]
  rw [map_mul, map_mul, hzero, hone] at hf
  exact AbelianEnumeratedPi02.swap_not_comm hf

/-- The protected free commutator is nonidentity. -/
theorem freeWitnessCommutator_ne_one : freeWitnessCommutator ≠ 1 := by
  intro h
  apply freeWitness_generators_not_commute
  exact commutatorElement_eq_one_iff_mul_comm.mp h

/-- The protected element belongs to the commutator subgroup. -/
theorem freeWitnessCommutator_mem_commutator :
    freeWitnessCommutator ∈ commutator FreeCommutatorWitness := by
  rw [commutator_eq_closure]
  exact Subgroup.subset_closure ⟨freeWitnessA, freeWitnessB, rfl⟩

/-- The free witness is finitely presented. -/
theorem freeCommutatorWitness_finitelyPresented :
    Group.IsFinitelyPresented FreeCommutatorWitness := by
  infer_instance

/-- The free witness is torsion-free. -/
theorem freeCommutatorWitness_torsionFree :
    IsPowerTorsionFree FreeCommutatorWitness :=
  IsPowerTorsionFree.of_isMulTorsionFree

/-- The exact package consumed by the simplified saturation construction. -/
theorem freeCommutatorWitness_package :
    Group.IsFinitelyPresented FreeCommutatorWitness ∧
      IsPowerTorsionFree FreeCommutatorWitness ∧
      freeWitnessCommutator ≠ 1 ∧
      freeWitnessCommutator ∈ commutator FreeCommutatorWitness :=
  ⟨freeCommutatorWitness_finitelyPresented,
    freeCommutatorWitness_torsionFree,
    freeWitnessCommutator_ne_one,
    freeWitnessCommutator_mem_commutator⟩

end TheoremC
end NonMF
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.TheoremC.freeCommutatorWitness_package
