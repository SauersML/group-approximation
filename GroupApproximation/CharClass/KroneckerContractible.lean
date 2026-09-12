import GroupApproximation.CharClass.KroneckerEquiv
import GroupApproximation.CharClass.CohomologyBridge

/-!
# A point is acyclic, over a field

Step 4a of the port: `H^k(Y; K) = 0` for `k ≥ 1` and `Y` contractible, and
`H^0(Y; K) ≃ₗ K`.  This is the base case of every Mayer–Vietoris computation downstream —
the trivialising pieces of a bundle, the hemispheres of a sphere, and the affine charts of
a projective space are all contractible — and it is half of what makes `H^*(CP^d; K)` a
line in each even degree.

## What this needs, and what it does not

`H_k(pt; K) = 0` for `k ≥ 1` is Mathlib's
`isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`, which is already generic in
the coefficient module.  Dualising it is `KroneckerEquiv.lean`.  Transporting along a
homotopy equivalence needs homotopy invariance, and that is **already generic in the
vendored layer**: `singularCohomologyMap_eq_of_homotopic (R) (M) (n)` takes
`(R : Type) [CommRing R]`, and the `ZMod 2` statements beneath it are thin
instantiations.  So this file is a restatement at the `Hmod K` level, not a reproof, and
the only new content is the two lines that name the right functor.

`[Field K]` comes in only through `kroneckerEquivOf`; the homotopy-invariance half is
`[CommRing K]`.
-/

open CategoryTheory AlgebraicTopology Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

namespace GroupApproximation
namespace CharClass

/-! ## 1. Homotopy invariance over `K` -/

/-- **Homotopy invariance.**  Homotopic maps have equal pullbacks on `H^n(−; K)`.  The
vendored `pull_eq_of_homotopic` is this at `K = ZMod 2`; the underlying prism operator was
already generic in the coefficient module. -/
theorem pull_eq_of_homotopicOf (K : Type) [CommRing K] {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : ContinuousMap.Homotopic f.hom g.hom) (n : ℕ) (a : Hmod K Y n) :
    pull f n a = pull g n a := by
  have hm := singularCohomologyMap_eq_of_homotopic K (ModuleCat.of K K) n h
  show ((singularCohomologyFunctor K (ModuleCat.of K K) n).map f.op).hom a
    = ((singularCohomologyFunctor K (ModuleCat.of K K) n).map g.op).hom a
  rw [hm]

/-- Homotopy invariance from a homotopy rather than the `Homotopic` relation. -/
theorem pull_eq_of_homotopyOf (K : Type) [CommRing K] {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (H : ContinuousMap.Homotopy f.hom g.hom) (n : ℕ) (a : Hmod K Y n) :
    pull f n a = pull g n a :=
  pull_eq_of_homotopicOf K ⟨H⟩ n a

/-- **A homotopy equivalence induces a linear isomorphism on `H^n(−; K)`.** -/
def pullEquivOfHomotopyEquivOf (K : Type) [CommRing K] {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    Hmod K (TopCat.of Y) n ≃ₗ[K] Hmod K (TopCat.of X) n :=
  LinearEquiv.ofLinear (pullLinear (cmap e.toFun) n) (pullLinear (cmap e.invFun) n)
    (by
      ext b
      show pull (cmap e.toFun) n (pull (cmap e.invFun) n b) = b
      rw [← pull_comp,
        show (cmap e.toFun ≫ cmap e.invFun) = cmap (e.invFun.comp e.toFun) from rfl,
        pull_eq_of_homotopicOf K (f := cmap (e.invFun.comp e.toFun)) (g := 𝟙 (TopCat.of X))
          e.left_inv n b, pull_id])
    (by
      ext a
      show pull (cmap e.invFun) n (pull (cmap e.toFun) n a) = a
      rw [← pull_comp,
        show (cmap e.invFun ≫ cmap e.toFun) = cmap (e.toFun.comp e.invFun) from rfl,
        pull_eq_of_homotopicOf K (f := cmap (e.toFun.comp e.invFun)) (g := 𝟙 (TopCat.of Y))
          e.right_inv n a, pull_id])

/-! ## 2. A point, and contractible spaces -/

/-- **`H^k(pt; K) = 0` for `k ≥ 1`.**  A point is totally disconnected, so its singular
homology vanishes above degree zero; the universal coefficient isomorphism dualises that. -/
theorem cohomology_unit_isZeroOf (K : Type) [Field K] (k : ℕ) (hk : 1 ≤ k) :
    IsZero (Hmod K (TopCat.of Unit) k) := by
  have hUnit :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat K) k (ModuleCat.of K K) (TopCat.of Unit) (by omega : k ≠ 0)
  change IsZero (homologyOf K (TopCat.of Unit) k) at hUnit
  exact IsZero.of_iso
    (homologyDualOf_isZero_of_homology_isZero K (TopCat.of Unit) k hUnit)
    (kroneckerEquivOf K (TopCat.of Unit) k)

/-- **`H^k(Y; K) = 0` for `k ≥ 1` and `Y` contractible.** -/
theorem cohomology_isZero_of_contractibleOf (K : Type) [Field K] (Y : Type)
    [TopologicalSpace Y] [ContractibleSpace Y] (k : ℕ) (hk : 1 ≤ k) :
    IsZero (Hmod K (TopCat.of Y) k) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit Y
  have h := cohomology_unit_isZeroOf K k hk
  rw [ModuleCat.isZero_iff_subsingleton] at h ⊢
  haveI := h
  exact (pullEquivOfHomotopyEquivOf K e k).toEquiv.symm.subsingleton

/-- Every class of `H^k(Y; K)`, `k ≥ 1`, `Y` contractible, is zero. -/
theorem cohomology_eq_zero_of_contractibleOf (K : Type) [Field K] (Y : Type)
    [TopologicalSpace Y] [ContractibleSpace Y] (k : ℕ) (hk : 1 ≤ k)
    (a : Hmod K (TopCat.of Y) k) : a = 0 := by
  have h := cohomology_isZero_of_contractibleOf K Y k hk
  rw [ModuleCat.isZero_iff_subsingleton] at h
  exact h.elim a 0

/-! ## 3. The `ZMod 2` instance is the vendored statement -/

theorem pull_eq_of_homotopicOf_zmod2 {X Y : TopCat.{0}} {f g : X ⟶ Y}
    (h : ContinuousMap.Homotopic f.hom g.hom) (n : ℕ) (a : Hmod2 Y n) :
    pull f n a = pull g n a :=
  pull_eq_of_homotopicOf (ZMod 2) h n a

theorem cohomology_unit_isZeroOf_zmod2 (k : ℕ) (hk : 1 ≤ k) :
    IsZero (Hmod2 (TopCat.of Unit) k) :=
  cohomology_unit_isZeroOf (ZMod 2) k hk

theorem cohomology_isZero_of_contractibleOf_zmod2 (Y : Type) [TopologicalSpace Y]
    [ContractibleSpace Y] (k : ℕ) (hk : 1 ≤ k) :
    IsZero (Hmod2 (TopCat.of Y) k) :=
  cohomology_isZero_of_contractibleOf (ZMod 2) Y k hk

end CharClass
end GroupApproximation

end
