import GroupApproximation.CharClass.ThomKunnethSphere
import GroupApproximation.CharClass.MayerVietorisVanishing
import GroupApproximation.CharClass.CohomologyProductCover
import GroupApproximation.CharClass.ProjectiveSpaceCover

/-!
# Complex projective space is a Künneth factor

`ThomPuncturedRecursion.KunnethFactor Y q` is the per-factor Künneth vanishing that the
punctured-product recursion consumes.  `ThomKunnethSphere.lean` supplies it for spheres
and for contractible spaces; this file supplies it for `ℂP^d`, which is the last input
of the recursion owed by anybody.

The proof is Mayer–Vietoris on the standard cover of `ℂP^{d+1}` crossed with the other
factor, by induction on `d`.  Writing `A` for the other factor:

* `A × chart` — the chart is contractible, so this contributes nothing;
* `A × (ℂP^{d+1} ∖ pt) ≃ A × ℂP^d` — the induction hypothesis;
* `A × (chart ∖ pt) ≃ A × S^{2d+1}` — the sphere Künneth factor.

**No δ-linearity is involved.**  Only the vanishing form of Mayer–Vietoris is used, so
this does not wait on `mvDelta_cup`; the module structure that Leray–Hirsch needs is a
strictly stronger statement than the one proved here.

## Main results

* `prodOpen_inf`, `isZero_prodOpen_of_homotopyEquiv` — plumbing for the product cover.
* `kunnethFactor_CP` — `KunnethFactor (CP d) (2 * d)` for every `d`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

noncomputable section

/-- The product cover respects intersections. -/
theorem prodOpen_inf (A : Type) [TopologicalSpace A] {Y : Type} [TopologicalSpace Y]
    (U V : Opens Y) : prodOpen A U ⊓ prodOpen A V = prodOpen A (U ⊓ V) := by
  ext p
  simp [prodOpen]

/-- Vanishing on a piece of the product cover, transported along a homotopy equivalence
of that piece. -/
theorem isZero_prodOpen_of_homotopyEquiv (A : Type) [TopologicalSpace A] {Y : Type}
    [TopologicalSpace Y] (U : Opens Y) {W : Type} [TopologicalSpace W]
    (e : ContinuousMap.HomotopyEquiv ↥(U : Set Y) W) (k : ℕ)
    (h : IsZero (Hmod2 (TopCat.of (A × W)) k)) :
    IsZero (Hmod2 (TopCat.of ↥((prodOpen A U : Opens (A × Y)) : Set (A × Y))) k) := by
  refine thomIsZero_of_linearEquiv (prodOpenCohEquiv A U k).symm ?_
  refine thomIsZero_of_linearEquiv (pullEquivOfHomotopyEquiv
    ((ContinuousMap.HomotopyEquiv.refl A).prodCongr e) k).symm ?_
  exact h

/-- **Complex projective space is a Künneth factor of its real dimension.** -/
theorem kunnethFactor_CP : ∀ d : ℕ, KunnethFactor (CP d) (2 * d) := by
  intro d
  induction d with
  | zero =>
    haveI : Unique (CP 0) := uniqueOfSubsingleton (Classical.arbitrary (CP 0))
    refine ⟨fun A _ p hA k hk => ?_⟩
    exact thomIsZero_of_linearEquiv
      (pullEquivOfHomeomorph (Homeomorph.prodUnique A (CP 0)) k).symm (hA k (by omega))
  | succ d ih =>
    haveI := contractibleSpace_chartOpen d
    refine ⟨fun A _ p hA k hk => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    refine isZero_cohomology_of_cover' (A × CP (d + 1))
      (prodOpen A (chartOpen d)) (prodOpen A (punctOpen d))
      (prodOpen_sup A (chartOpen_sup_punctOpen d)) m ?_ ?_ ?_
    · rw [prodOpen_inf]
      refine isZero_prodOpen_of_homotopyEquiv A (chartOpen d ⊓ punctOpen d)
        (interSphereHomotopyEquiv d) m ?_
      exact (kunnethFactor_sphere (2 * d + 1)).prod A p hA m (by omega)
    · exact isZero_prodOpen_of_contractible A (chartOpen d) (m + 1) (hA (m + 1) (by omega))
    · refine isZero_prodOpen_of_homotopyEquiv A (punctOpen d)
        (punctOpenHomotopyEquiv d) (m + 1) ?_
      exact ih.prod A p hA (m + 1) (by omega)

end

end GroupApproximation.CharClass
