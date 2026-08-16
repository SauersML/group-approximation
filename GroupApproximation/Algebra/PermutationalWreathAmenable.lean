import GroupApproximation.Algebra.PermutationalWreath
import GroupApproximation.Algebra.Amenable

/-!
# The lamp group of a finite lamp is amenable

Part of the permanence package of Section 54.2: over a finite lamp group the
configuration group `K^{(X)}` is locally finite -- every finite set of
configurations is supported on finitely many sites -- hence amenable.

Together with `lamp_isResiduallyFinite` and `suppIn_finite` this pins down how
tame the kernel of the split extension is: locally finite, amenable, residually
finite.  What fails in the wreath product is not the kernel but the extension.
-/

namespace GroupApproximation

universe u v

variable {K : Type u} [Group K] {X : Type v}

/-- Finitely many lamp configurations are supported on finitely many sites. -/
theorem lamp_closure_finite [Finite K] (S : Finset (Lamp K X)) :
    (Subgroup.closure (S : Set (Lamp K X)) : Set (Lamp K X)).Finite := by
  classical
  have hsupp : ∀ f : Lamp K X, {x : X | (f : X → K) x ≠ 1}.Finite := fun f => f.2
  set T : Finset X := S.biUnion (fun f => (hsupp f).toFinset) with hT
  have hle : Subgroup.closure (S : Set (Lamp K X)) ≤ suppIn (K := K) T := by
    rw [Subgroup.closure_le]
    intro f hf
    rw [SetLike.mem_coe, mem_suppIn]
    intro x hx
    by_contra hcon
    exact hx (Finset.mem_biUnion.mpr ⟨f, hf, (Set.Finite.mem_toFinset _).mpr hcon⟩)
  haveI : Finite ↥(suppIn (K := K) T) := suppIn_finite T
  exact Set.Finite.subset (Set.toFinite _) hle

/-- **Section 54.2.**  The lamp group of a finite lamp group is amenable. -/
theorem lamp_isAmenable [Finite K] :
    Amenability.IsAmenable (Lamp K X) :=
  Amenability.isAmenable_of_locallyFinite lamp_closure_finite

end GroupApproximation
