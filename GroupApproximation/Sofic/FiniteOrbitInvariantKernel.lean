import GroupApproximation.Sofic.CliffordLampPermanence
import GroupApproximation.Sofic.SoficInvariantFiniteKernel
import Mathlib.Algebra.Group.Pointwise.Set.Finite

/-!
# Finite-orbit kernels

This file turns the geometric input used by the Clifford witness into the
exact finite invariant subgroups required by the local semidirect-product
permanence theorem.

There are two elementary steps.  First, the elements having finite orbit
under an action by automorphisms form a subgroup.  Hence, if every site has
finite orbit, then every element of the presented Clifford lamp group has
finite orbit: the sign is fixed and the orbit of a lamp is the image of the
corresponding site orbit.  Second, in a locally finite group, finitely many
finite orbits generate a finite invariant subgroup.

Keeping these facts separate from the telescope calculation avoids choosing
normal forms for the presented Clifford group.
-/

namespace GroupApproximation

open scoped Pointwise

universe u v w

variable {H : Type u} {N : Type v} [Group H] [Group N]

/-- Elements with finite orbit under an action by automorphisms. -/
def finiteOrbitSubgroup (ψ : H →* MulAut N) : Subgroup N where
  carrier := {n | (Set.range fun h : H ↦ ψ h n).Finite}
  one_mem' := by
    refine (Set.finite_singleton (1 : N)).subset ?_
    rintro _ ⟨h, rfl⟩
    simp
  mul_mem' := by
    intro a b ha hb
    refine (ha.mul hb).subset ?_
    rintro _ ⟨h, rfl⟩
    change ψ h (a * b) ∈
      (Set.range fun k : H ↦ ψ k a) * Set.range fun k : H ↦ ψ k b
    rw [map_mul]
    exact Set.mul_mem_mul ⟨h, rfl⟩ ⟨h, rfl⟩
  inv_mem' := by
    intro a ha
    refine (ha.image fun n : N ↦ n⁻¹).subset ?_
    rintro _ ⟨h, rfl⟩
    exact ⟨ψ h a, ⟨⟨h, rfl⟩, (map_inv (ψ h) a).symm⟩⟩

/-- Finite orbits of a finite window generate a finite invariant subgroup in
a locally finite group. -/
theorem exists_finite_invariant_subgroup_of_finite_orbits
    (ψ : H →* MulAut N) (hN : IsLocallyFiniteGroup N)
    (horbit : ∀ n : N, (Set.range fun h : H ↦ ψ h n).Finite)
    (F : Finset N) :
    ∃ K : Subgroup N, Finite K ∧
      (∀ h : H, ∀ n ∈ K, ψ h n ∈ K) ∧ ∀ n ∈ F, n ∈ K := by
  classical
  let S : Set N := ⋃ n ∈ (F : Set N), Set.range fun h : H ↦ ψ h n
  have hSfin : S.Finite :=
    Set.Finite.biUnion F.finite_toSet fun n _ ↦ horbit n
  obtain ⟨L, hLfin, hSL⟩ := hN hSfin.toFinset
  letI : Finite L := hLfin
  let K : Subgroup N := Subgroup.closure S
  have hKle : K ≤ L := by
    change Subgroup.closure S ≤ L
    rw [Subgroup.closure_le]
    intro n hn
    exact hSL n (hSfin.mem_toFinset.mpr hn)
  have hKfin : Finite K :=
    Finite.of_injective
      (fun n : K ↦ (⟨n, hKle n.2⟩ : L))
      (fun a b h ↦ Subtype.ext
        (show (a : N) = (b : N) from congrArg (fun x : L ↦ (x : N)) h))
  refine ⟨K, hKfin, ?_, ?_⟩
  · intro h n hn
    induction hn using Subgroup.closure_induction with
    | mem n hn =>
        apply Subgroup.subset_closure
        rcases Set.mem_iUnion.mp hn with ⟨a, hn⟩
        rcases Set.mem_iUnion.mp hn with ⟨ha, hn⟩
        rcases hn with ⟨k, rfl⟩
        exact Set.mem_iUnion_of_mem a
          (Set.mem_iUnion_of_mem ha ⟨h * k, by
            change ψ (h * k) a = ψ h (ψ k a)
            rw [map_mul, MulAut.mul_apply]⟩)
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
    | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha
  · intro n hn
    apply Subgroup.subset_closure
    exact Set.mem_iUnion_of_mem n
      (Set.mem_iUnion_of_mem (Finset.mem_coe.mpr hn) ⟨1, by
        change ψ 1 n = n
        rw [map_one]
        rfl⟩)

namespace CliffordLamp

variable {X : Type w}

/-- An action on sites induces the permutation action on Clifford lamps. -/
def actionHom (ρ : H →* Equiv.Perm X) : H →* MulAut (CliffordLamp X) :=
  (permHom X).comp ρ

@[simp] theorem actionHom_apply_sign (ρ : H →* Equiv.Perm X) (h : H) :
    actionHom ρ h (sign X) = sign X := by
  simp [actionHom]

@[simp] theorem actionHom_apply_lamp (ρ : H →* Equiv.Perm X) (h : H) (x : X) :
    actionHom ρ h (lamp X x) = lamp X (ρ h x) := by
  simp [actionHom]

/-- If every site orbit is finite, every Clifford-lamp element has finite
orbit. -/
theorem finite_orbit_of_finite_site_orbits (ρ : H →* Equiv.Perm X)
    (hsite : ∀ x : X, (Set.range fun h : H ↦ ρ h x).Finite)
    (n : CliffordLamp X) :
    (Set.range fun h : H ↦ actionHom ρ h n).Finite := by
  let P := finiteOrbitSubgroup (actionHom ρ)
  show n ∈ P
  apply mem_subgroup_of_sign_mem_of_lamp_mem X P
  · show (Set.range fun h : H ↦ actionHom ρ h (sign X)).Finite
    refine (Set.finite_singleton (sign X)).subset ?_
    rintro _ ⟨h, rfl⟩
    simp
  · intro x
    show (Set.range fun h : H ↦ actionHom ρ h (lamp X x)).Finite
    refine (hsite x).image (lamp X) |>.subset ?_
    rintro _ ⟨h, rfl⟩
    exact ⟨ρ h x, ⟨⟨h, rfl⟩, (actionHom_apply_lamp ρ h x).symm⟩⟩

/-- Finite site orbits give the finite invariant Clifford subgroups used by
the witness soficity argument. -/
theorem exists_finite_invariant_clifford_subgroup
    (ρ : H →* Equiv.Perm X)
    (hsite : ∀ x : X, (Set.range fun h : H ↦ ρ h x).Finite)
    (F : Finset (CliffordLamp X)) :
    ∃ K : Subgroup (CliffordLamp X), Finite K ∧
      (∀ h : H, ∀ n ∈ K, actionHom ρ h n ∈ K) ∧
      ∀ n ∈ F, n ∈ K :=
  exists_finite_invariant_subgroup_of_finite_orbits
    (actionHom ρ) (isLocallyFiniteGroup_cliffordLamp X)
    (finite_orbit_of_finite_site_orbits ρ hsite) F

end CliffordLamp
end GroupApproximation
