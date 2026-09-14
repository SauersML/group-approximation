import GroupApproximation.Manuscript.SimpleKazhdanSofic.Setting
import GroupApproximation.Dynamics.SubshiftFiniteWindow
import GroupApproximation.Meta.AxiomGuard

/-!
# Minimal subshifts have dense orbits

`simple_kazhdan_sofic_group.tex` (origin/main tip), Theorem `thm:main`: `X` is a minimal subshift,
that is, it has no nonempty proper closed shift-invariant subset (`SimpleKazhdanSofic.IsMinimal`).
The general simplicity results of `GroupApproximation/Pestov91` read minimality as density of every
orbit of the shift.  This module proves that reading.

* `subshiftHomeo_zpow_apply`: `(T ^ j) x` is `shift j x`, from `WordGraph.zpow_apply_coord`.
* `orbitClosureImage_isClosed`, `orbitClosureImage_subset`, `orbitClosureImage_mapsTo`: the image in
  `A^ℤ` of the closure of an orbit is closed, lies in `X`, and is shift-invariant.
* `minimalSubshift_dense_orbits`: in a minimal subshift every orbit of the shift is dense.

## Manuscript status

Intermediate: minimality in the form the general simplicity theorem consumes, for the assembly of
`thm:main`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open SymbolicDynamics.FullShift Set

variable {A : Type} [TopologicalSpace A]

/-- `(T ^ j) x` is `shift j x`. -/
theorem subshiftHomeo_zpow_apply (S : Subshift A ℤ) (j : ℤ) (x : S.carrier) :
    ((subshiftHomeo S ^ j) x).1 = shift j x.1 := by
  funext m
  rw [shift_apply]
  exact WordGraph.zpow_apply_coord (T := subshiftHomeo S) (fun _ => rfl) j x m

/-- The image in `A^ℤ` of the closure of the orbit of `x`. -/
def orbitClosureImage (S : Subshift A ℤ) (x : S.carrier) : Set (ℤ → A) :=
  Subtype.val '' closure (Set.range fun j : ℤ => (subshiftHomeo S ^ j) x)

theorem orbitClosureImage_isClosed (S : Subshift A ℤ) (x : S.carrier) :
    IsClosed (orbitClosureImage S x) :=
  S.isClosed.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_closure

theorem orbitClosureImage_subset (S : Subshift A ℤ) (x : S.carrier) :
    orbitClosureImage S x ⊆ S.carrier := by
  rintro _ ⟨z, -, rfl⟩
  exact z.2

theorem orbitClosureImage_mapsTo (S : Subshift A ℤ) (x : S.carrier) (g : ℤ) :
    MapsTo (shift g) (orbitClosureImage S x) (orbitClosureImage S x) := by
  have horbit : MapsTo (subshiftHomeo S ^ g) (Set.range fun j : ℤ => (subshiftHomeo S ^ j) x)
      (Set.range fun j : ℤ => (subshiftHomeo S ^ j) x) := by
    rintro _ ⟨j, rfl⟩
    refine ⟨g + j, ?_⟩
    show (subshiftHomeo S ^ (g + j)) x = (subshiftHomeo S ^ g) ((subshiftHomeo S ^ j) x)
    rw [zpow_add, Homeomorph.mul_apply]
  have hcl := horbit.closure (subshiftHomeo S ^ g).continuous
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨(subshiftHomeo S ^ g) z, hcl hz, subshiftHomeo_zpow_apply S g z⟩

/-- **In a minimal subshift every orbit of the shift is dense.** -/
theorem minimalSubshift_dense_orbits (S : Subshift A ℤ) (hmin : IsMinimal S) (x : S.carrier) :
    Dense (Set.range fun j : ℤ => (subshiftHomeo S ^ j) x) := by
  rcases hmin (orbitClosureImage S x) (orbitClosureImage_isClosed S x)
      (orbitClosureImage_subset S x) (orbitClosureImage_mapsTo S x) with hempty | hall
  · exfalso
    have hx : x.1 ∈ orbitClosureImage S x :=
      ⟨x, subset_closure ⟨0, show (subshiftHomeo S ^ (0 : ℤ)) x = x by
        rw [zpow_zero, Homeomorph.one_apply]⟩, rfl⟩
    rw [hempty] at hx
    exact hx
  · rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro z
    have hz : z.1 ∈ orbitClosureImage S x := by
      rw [hall]
      exact z.2
    obtain ⟨w, hw, hwz⟩ := hz
    rwa [Subtype.ext hwz] at hw

end SimpleKazhdanSofic
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.SimpleKazhdanSofic.subshiftHomeo_zpow_apply
#audit_axioms GroupApproximation.SimpleKazhdanSofic.minimalSubshift_dense_orbits
