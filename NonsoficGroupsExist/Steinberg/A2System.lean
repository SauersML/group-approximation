import NonsoficGroupsExist.Steinberg.Basic
import NonsoficGroupsExist.PropertyT.A2System

/-!
# The Steinberg root system of type A₂

The six root subgroups of `St₃(R)` form the same strongly graded `A₂`
system as their elementary images.  Unlike a transfer from `EL₃(R)`, this
construction retains the full central Steinberg kernel.
-/

namespace NonsoficGroupsExist
namespace SteinbergGroup

open scoped commutatorElement

variable {R : Type*} [Ring R]

/-- The additive Steinberg root subgroup `Xᵢⱼ`. -/
def rootSubgroup (i j : Fin 3) (hij : i ≠ j) :
    Subgroup (SteinbergGroup (Fin 3) R) where
  carrier := Set.range (x i j hij)
  one_mem' := ⟨0, x_zero i j hij⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, (x_mul i j hij a b).symm⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, x_neg i j hij a⟩

theorem mem_rootSubgroup_iff (i j : Fin 3) (hij : i ≠ j)
    (g : SteinbergGroup (Fin 3) R) :
    g ∈ rootSubgroup i j hij ↔ ∃ a : R, x i j hij a = g :=
  Iff.rfl

/-- The union of the six Steinberg root subgroups. -/
def rootSet : Set (SteinbergGroup (Fin 3) R) :=
  {g | ∃ (i j : Fin 3) (hij : i ≠ j), g ∈ rootSubgroup i j hij}

/-- The six root subgroups generate the full presented Steinberg group. -/
theorem rootSet_generate : Subgroup.closure (rootSet (R := R)) = ⊤ := by
  have hgen := PresentedGroup.closure_range_of
    (relations (I := Fin 3) (R := R))
  rw [← hgen]
  congr 1
  ext g
  constructor
  · rintro ⟨i, j, hij, a, ha⟩
    refine ⟨⟨i, j, hij, a⟩, ?_⟩
    simpa only [x_eq_of] using ha
  · rintro ⟨q, rfl⟩
    rcases q with ⟨i, j, hij, a⟩
    exact ⟨i, j, hij, a, rfl⟩

/-- The strongly graded `A₂` system inside `St₃(R)`. -/
def a2System : A2System (SteinbergGroup (Fin 3) R) where
  root := fun i j hij ↦ rootSubgroup i j hij
  generate := rootSet_generate
  commute := by
    intro i j k l hij hkl hjk hli u hu v hv
    obtain ⟨a, rfl⟩ := hu
    obtain ⟨b, rfl⟩ := hv
    exact x_commute_of_ne i j k l hij hkl hjk hli a b
  commutator_mem := by
    intro i j k hij hjk hik u hu v hv
    obtain ⟨a, rfl⟩ := hu
    obtain ⟨b, rfl⟩ := hv
    exact ⟨a * b, (x_commutator i j k hij hjk hik a b).symm⟩
  commutator_surjective := by
    intro i j k hij hjk hik z hz
    obtain ⟨a, rfl⟩ := hz
    refine ⟨x i j hij a, ⟨a, rfl⟩,
      x j k hjk 1, ⟨1, rfl⟩, ?_⟩
    simpa using x_commutator i j k hij hjk hik a 1

end SteinbergGroup
end NonsoficGroupsExist
