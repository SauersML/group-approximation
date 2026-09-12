import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.FreeRing

/-!
# Free presentations of finitely generated rings

`GroupApproximation.Steinberg.FiniteTypePropertyT` presents a finite-type
`𝔽₂`-algebra as a quotient of a free `𝔽₂`-algebra on a finite type, using
`Algebra.FiniteType.iff_quotient_freeAlgebra'`.  That step is the only reason
the direct property-`(T)` chain is restricted to characteristic two.  This file
supplies the base-change half of removing the restriction: the same
presentation over the initial ring `ℤ`, which needs no algebra structure on the
coefficient ring at all.

Every ring is a `ℤ`-algebra (`Ring.toIntAlgebra`), and a `ℤ`-subalgebra of a
ring is the same thing as a subring (`Algebra.adjoin_int`).  Consequently
`Algebra.FiniteType ℤ R` is *literally* the elementary statement "`R` is
generated as a unital ring by finitely many elements": this is
`finiteType_int_iff_exists_finset_subring_closure_eq_top` below.  No extra
hypothesis is needed anywhere — in particular no commutativity, no
Noetherianity, and no torsion or characteristic assumption.

Two free objects are available and both are covered:

* `FreeAlgebra ℤ X`, matching the shape of the characteristic-two argument;
* `FreeRing X`, Mathlib's free unital associative ring, whose universal
  property `FreeRing.lift` maps into an arbitrary `Ring` with no algebra
  structure in sight.

Mathlib's pinned version has no isomorphism `FreeRing X ≃+* FreeAlgebra ℤ X`,
so the two presentations are proved independently rather than transported
across one.

The transport half — that a surjection of coefficient rings induces a
surjection of Steinberg groups — is already available in full generality as
`GroupApproximation.SteinbergGroup.ringMap_surjective_of_surjective`, which is
stated for an arbitrary ring homomorphism between arbitrary rings; it is not
restated here.
-/

namespace GroupApproximation

universe u

variable (R : Type u) [Ring R]

/-- For a ring `R`, viewed as a `ℤ`-algebra via `Ring.toIntAlgebra`, the
Mathlib finiteness condition `Algebra.FiniteType ℤ R` is exactly the elementary
statement that finitely many elements generate `R` as a unital ring.  Both
directions are `Algebra.adjoin_int`: adjoining a set to the image of `ℤ` is the
same as generating a subring. -/
theorem finiteType_int_iff_exists_finset_subring_closure_eq_top :
    Algebra.FiniteType ℤ R ↔ ∃ s : Finset R, Subring.closure (s : Set R) = ⊤ := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := h.out
    refine ⟨s, ?_⟩
    rw [Subring.eq_top_iff']
    intro y
    have hy : y ∈ Algebra.adjoin ℤ (s : Set R) := by
      rw [hs]
      exact Algebra.mem_top
    rw [Algebra.adjoin_int] at hy
    exact mem_subalgebraOfSubring.mp hy
  · rintro ⟨s, hs⟩
    refine ⟨⟨s, ?_⟩⟩
    rw [Algebra.adjoin_int, hs, Algebra.eq_top_iff]
    intro y
    exact mem_subalgebraOfSubring.mpr (Subring.mem_top y)

/-- Every finitely generated unital associative ring is a quotient of a free
`ℤ`-algebra on a finite type.  This is the `ℤ`-algebra analogue of the
characteristic-two step in `FiniteTypePropertyT`, and it is unconditional: by
`finiteType_int_iff_exists_finset_subring_closure_eq_top` the hypothesis is
just finite generation as a ring. -/
theorem exists_finite_freeAlgebraInt_surjection [Algebra.FiniteType ℤ R] :
    ∃ (X : Type u) (_ : Fintype X) (f : FreeAlgebra ℤ X →ₐ[ℤ] R),
      Function.Surjective f :=
  (Algebra.FiniteType.iff_quotient_freeAlgebra' (R := ℤ) (A := R)).mp inferInstance

/-- Ring-homomorphism form of `exists_finite_freeAlgebraInt_surjection`, which
is the shape consumed by `SteinbergGroup.ringMap`. -/
theorem exists_finite_freeAlgebraInt_ringHom_surjection [Algebra.FiniteType ℤ R] :
    ∃ (X : Type u) (_ : Fintype X) (f : FreeAlgebra ℤ X →+* R),
      Function.Surjective f := by
  obtain ⟨X, hX, f, hf⟩ := exists_finite_freeAlgebraInt_surjection R
  exact ⟨X, hX, f.toRingHom, hf⟩

/-- If the finite set `s` generates `R` as a unital ring, then the ring
homomorphism out of the free ring on `s` induced by the inclusion of `s` is
surjective.  This uses only the universal property `FreeRing.lift`, so no
algebra structure on `R` is involved. -/
theorem freeRing_lift_coe_surjective (s : Finset R)
    (hs : Subring.closure (s : Set R) = ⊤) :
    Function.Surjective (FreeRing.lift (fun a : {x : R // x ∈ s} => (a : R))) := by
  have hle : Subring.closure (s : Set R) ≤
      (FreeRing.lift (fun a : {x : R // x ∈ s} => (a : R))).range := by
    refine Subring.closure_le.mpr ?_
    intro a ha
    exact SetLike.mem_coe.mpr (RingHom.mem_range.mpr
      ⟨FreeRing.of ⟨a, Finset.mem_coe.mp ha⟩, FreeRing.lift_of _ _⟩)
  rw [hs] at hle
  exact RingHom.range_eq_top.mp (top_le_iff.mp hle)

/-- Every finitely generated unital associative ring is a quotient of a free
ring on a finite type. -/
theorem exists_finite_freeRing_surjection
    (hfg : ∃ s : Finset R, Subring.closure (s : Set R) = ⊤) :
    ∃ (X : Type u) (_ : Fintype X) (f : FreeRing X →+* R),
      Function.Surjective f := by
  obtain ⟨s, hs⟩ := hfg
  exact ⟨{x : R // x ∈ s}, inferInstance,
    FreeRing.lift (fun a : {x : R // x ∈ s} => (a : R)),
    freeRing_lift_coe_surjective R s hs⟩

/-- The free-ring presentation phrased with Mathlib's finiteness class, for
uniformity with `exists_finite_freeAlgebraInt_surjection`. -/
theorem exists_finite_freeRing_surjection_of_finiteType [Algebra.FiniteType ℤ R] :
    ∃ (X : Type u) (_ : Fintype X) (f : FreeRing X →+* R),
      Function.Surjective f :=
  exists_finite_freeRing_surjection R
    ((finiteType_int_iff_exists_finset_subring_closure_eq_top R).mp inferInstance)

end GroupApproximation
