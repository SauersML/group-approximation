import GroupApproximation.Steinberg.A2System
import GroupApproximation.PropertyT.FreeAlgebraDegree

/-!
# Finite degree stages of Steinberg root subgroups

The finite-control proof filters each additive Steinberg root by word degree
in a finite free algebra.  These finite stages increase to the full root
subgroup.  This is the Steinberg analogue of the elementary-root filtration,
but it is constructed directly from the presented generators `xᵢⱼ(a)` and
therefore retains the full Steinberg kernel.
-/

namespace GroupApproximation
namespace SteinbergGroup

open FreeAlgebraDegree

variable (X : Type*) [Fintype X]
variable (K : Type*) [CommRing K]

/-- The Steinberg root elements whose coefficients have word degree at most
`n`. -/
def rootDegreeSubgroup (i j : Fin 3) (hij : i ≠ j) (n : ℕ) :
    Subgroup (SteinbergGroup (Fin 3) (FreeAlgebra K X)) where
  carrier := {g | ∃ a : FreeAlgebra K X,
    a ∈ degreeLE X K n ∧ x i j hij a = g}
  one_mem' := ⟨0, (degreeLE X K n).zero_mem, x_zero i j hij⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, (degreeLE X K n).add_mem ha hb,
      (x_mul i j hij a b).symm⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, (degreeLE X K n).neg_mem ha, x_neg i j hij a⟩

theorem mem_rootDegreeSubgroup_iff
    (i j : Fin 3) (hij : i ≠ j) (n : ℕ)
    (g : SteinbergGroup (Fin 3) (FreeAlgebra K X)) :
    g ∈ rootDegreeSubgroup X K i j hij n ↔
      ∃ a : FreeAlgebra K X,
        a ∈ degreeLE X K n ∧ x i j hij a = g :=
  Iff.rfl

/-- Every degree-bounded Steinberg root subgroup over finite coefficients is
finite. -/
noncomputable instance finite_rootDegreeSubgroup [Finite K]
    (i j : Fin 3) (hij : i ≠ j) (n : ℕ) :
    Finite (rootDegreeSubgroup X K i j hij n) := by
  let f : degreeLE X K n → rootDegreeSubgroup X K i j hij n := fun a ↦
    ⟨x i j hij a.1, ⟨a.1, a.2, rfl⟩⟩
  exact Finite.of_surjective f (by
    rintro ⟨g, a, ha, hag⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    exact hag)

/-- Root degree stages form an increasing sequence of subgroups. -/
theorem rootDegreeSubgroup_mono (i j : Fin 3) (hij : i ≠ j) :
    Monotone (rootDegreeSubgroup X K i j hij) := by
  intro m n hmn g
  rintro ⟨a, ha, hag⟩
  exact ⟨a, degreeLE_mono X K hmn ha, hag⟩

theorem rootDegreeSubgroup_le (i j : Fin 3) (hij : i ≠ j) (n : ℕ) :
    rootDegreeSubgroup X K i j hij n ≤ rootSubgroup i j hij := by
  rintro g ⟨a, _, rfl⟩
  exact ⟨a, rfl⟩

/-- The finite degree stages exhaust the full Steinberg root subgroup. -/
theorem iSup_rootDegreeSubgroup (i j : Fin 3) (hij : i ≠ j) :
    ⨆ n, rootDegreeSubgroup X K i j hij n = rootSubgroup i j hij := by
  apply le_antisymm
  · exact iSup_le (rootDegreeSubgroup_le X K i j hij)
  · intro g hg
    obtain ⟨a, rfl⟩ := hg
    obtain ⟨n, hn⟩ := exists_mem_degreeLE X K a
    exact (le_iSup (rootDegreeSubgroup X K i j hij) n) ⟨a, hn, rfl⟩

end SteinbergGroup
end GroupApproximation
