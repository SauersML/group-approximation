import GroupApproximation.CharClass.ThomKunnethProjective
import GroupApproximation.CharClass.CohomologyKunnethSphereOf
import GroupApproximation.CharClass.ThomToolkitInstanceOf
import GroupApproximation.Meta.AxiomGuard

/-!
# Spheres and complex projective spaces are Künneth factors over a field

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

The punctured-product recursion (`PuncturedAcyclicOf.prod`) asks for the second factor of
each product to be a Künneth factor: the cohomology of `A × Y` vanishes above `p + q`
whenever that of `A` vanishes above `p`.  At `F₂`, `ThomKunnethSphere` and
`ThomKunnethProjective` supply this for `Y = S^n` and `Y = ℂP^d`.  Over a field `K` the
same arguments run on `lix-coeff`'s `K`-forms:

* for spheres, induction on the dimension: `S⁰` is two contractible halves with empty
  intersection (`isZero_mvAmbientOf`, `isZero_cohomology_of_isEmptyOf`), and the step is
  `isZero_prod_sphere_succOf`;
* for `ℂP^d`, induction on `d` over the cover by the affine chart and the punctured space,
  whose intersection is the odd sphere and whose punctured piece retracts onto `ℂP^{d-1}`
  (`cohomologyToolkitOf K` for Mayer–Vietoris).

These are the Künneth inputs of `hacyclic` in Step C over `F_p`, for the base
`S^{2n+1} × ∏ ℂP^{dᵢ}` of the LIX tower.

## Main declarations

* `kunnethFactor_sphereOf` — `S^n` is a Künneth factor of dimension `n` over a field.
* `isZero_prodOpen_of_homotopyEquivOf` — vanishing on a piece of the product cover,
  transported along a homotopy equivalence.
* `kunnethFactor_CPOf` — `ℂP^d` is a Künneth factor of dimension `2d` over a field.
-/

set_option autoImplicit false

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

set_option maxHeartbeats 1000000 in
/-- **A sphere is a Künneth factor of its own dimension, over a field.** -/
theorem kunnethFactor_sphereOf (K : Type) [Field K] (n : ℕ) :
    KunnethFactorOf K (Sphere n) n := by
  refine ⟨fun A _ p hA k hk => ?_⟩
  have hbase : ∀ m : ℕ, IsZero (Hmod K (TopCat.of A) (m + 1)) →
      IsZero (Hmod K (TopCat.of (A × Sphere 0)) (m + 1)) := by
    intro m hAm
    refine isZero_mvAmbientOf K (prodOpen A sphereZeroPos) (prodOpen A sphereZeroNeg)
      (prodOpen_sup A sphereZero_sup) m ?_
      (isZero_prodOpen_of_contractibleOf K A sphereZeroPos (m + 1) hAm)
      (isZero_prodOpen_of_contractibleOf K A sphereZeroNeg (m + 1) hAm)
    rw [prodOpen_coe_inter, sphereZero_inter_empty, Set.preimage_empty]
    exact isZero_cohomology_of_isEmptyOf K _ m
  have key : ∀ j k : ℕ, p + j < k → IsZero (Hmod K (TopCat.of (A × Sphere j)) k) := by
    intro j
    induction j with
    | zero =>
        intro k hk
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        exact hbase m (hA (m + 1) (by omega))
    | succ j ih =>
        intro k hk
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        exact isZero_prod_sphere_succOf K A j m (ih m (by omega)) (hA (m + 1) (by omega))
  exact key n k hk

/-- Vanishing on a piece of the product cover, transported along a homotopy equivalence of
that piece, over any commutative ring. -/
theorem isZero_prodOpen_of_homotopyEquivOf (K : Type) [CommRing K] (A : Type)
    [TopologicalSpace A] {Y : Type} [TopologicalSpace Y] (U : Opens Y) {W : Type}
    [TopologicalSpace W] (e : ContinuousMap.HomotopyEquiv ↥(U : Set Y) W) (k : ℕ)
    (h : IsZero (Hmod K (TopCat.of (A × W)) k)) :
    IsZero (Hmod K (TopCat.of ↥((prodOpen A U : Opens (A × Y)) : Set (A × Y))) k) := by
  refine thomIsZero_of_linearEquiv (prodOpenCohEquivOf K A U k).symm ?_
  refine thomIsZero_of_linearEquiv (pullEquivOfHomotopyEquivOf K
    ((ContinuousMap.HomotopyEquiv.refl A).prodCongr e) k).symm ?_
  exact h

/-- **Complex projective space is a Künneth factor of its real dimension, over a field.** -/
theorem kunnethFactor_CPOf (K : Type) [Field K] : ∀ d : ℕ, KunnethFactorOf K (CP d) (2 * d) := by
  intro d
  induction d with
  | zero =>
    haveI : Unique (CP 0) := uniqueOfSubsingleton (Classical.arbitrary (CP 0))
    refine ⟨fun A _ p hA k hk => ?_⟩
    exact thomIsZero_of_linearEquiv
      (pullEquivOfHomotopyEquivOf K (Homeomorph.prodUnique A (CP 0)).toHomotopyEquiv k).symm
      (hA k (by omega))
  | succ d ih =>
    haveI := contractibleSpace_chartOpen d
    refine ⟨fun A _ p hA k hk => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    refine (cohomologyToolkitOf K).mv (A × CP (d + 1))
      (prodOpen A (chartOpen d)) (prodOpen A (punctOpen d))
      (prodOpen_sup A (chartOpen_sup_punctOpen d)) m ?_ ?_ ?_
    · rw [prodOpen_inf]
      refine isZero_prodOpen_of_homotopyEquivOf K A (chartOpen d ⊓ punctOpen d)
        (interSphereHomotopyEquiv d) m ?_
      exact (kunnethFactor_sphereOf K (2 * d + 1)).prod A p hA m (by omega)
    · exact isZero_prodOpen_of_contractibleOf K A (chartOpen d) (m + 1) (hA (m + 1) (by omega))
    · refine isZero_prodOpen_of_homotopyEquivOf K A (punctOpen d)
        (punctOpenHomotopyEquiv d) (m + 1) ?_
      exact ih.prod A p hA (m + 1) (by omega)

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms kunnethFactor_sphereOf
#audit_axioms kunnethFactor_CPOf

end

end GroupApproximation.CharClass
