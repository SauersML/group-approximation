import GroupApproximation.Analysis.LIXLimitCompletion

/-!
# The inductive limit of separable C⋆-algebras is separable

A bonus conjunct for the STW Problem LIX endpoint.  The stage algebras of the LIX tower are
corners of `M_K(C(X))` with `X` compact metrizable, hence separable; separability of the limit
follows formally, in two steps that use nothing about the tower:

* the *algebraic* colimit is separable, because it is the union of the countably many images
  `ι_i (A i)` and each of those is the continuous image of a separable space;
* the completion of a separable space is separable, because the canonical map is continuous with
  dense range.

Nothing here needs the C⋆-structure beyond the continuity of `ι_i`, which is isometry.
-/

namespace GroupApproximation

namespace LIX

namespace CStarTower

open TopologicalSpace

universe u

noncomputable section

variable {A : ℕ → Type u} [∀ n, CStarAlgebra (A n)] (T : CStarTower A)

/-- The algebraic colimit of a tower of separable C⋆-algebras is separable: the union of the
images of countable dense subsets of the levels is countable, and dense because every element of
the colimit comes from a level. -/
theorem separableSpace_colim [∀ n, SeparableSpace (A n)] : SeparableSpace T.Colim := by
  choose D hDcount hDdense using fun n : ℕ => exists_countable_dense (A n)
  refine ⟨⟨⋃ n, T.iota n '' D n, Set.countable_iUnion fun n => (hDcount n).image _, ?_⟩⟩
  intro z
  obtain ⟨i, a, rfl⟩ := T.exists_mkAt z
  have hmem : T.iota i a ∈ T.iota i '' closure (D i) := ⟨a, hDdense i a, rfl⟩
  have h₂ := image_closure_subset_closure_image (T.iota_isometry i).continuous hmem
  exact closure_mono (Set.subset_iUnion (fun n => T.iota n '' D n) i) h₂

/-- The inductive limit of a tower of separable C⋆-algebras is separable. -/
instance separableSpace_limit [∀ n, SeparableSpace (A n)] : SeparableSpace T.Limit := by
  haveI := T.separableSpace_colim
  have hcont : Continuous (CStarCompletion.coeStarAlgHom T.Colim) :=
    (AddMonoidHomClass.isometry_of_norm _
      (CStarCompletion.norm_coeStarAlgHom T.Colim)).continuous
  exact (CStarCompletion.denseRange_coeStarAlgHom T.Colim).separableSpace hcont

end

end CStarTower

end LIX

end GroupApproximation
