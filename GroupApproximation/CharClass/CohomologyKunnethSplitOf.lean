import GroupApproximation.CharClass.CohomologyKunnethMap
import GroupApproximation.CharClass.KroneckerSphere
import GroupApproximation.Meta.AxiomGuard

/-!
# The Künneth map with a sphere factor, over any field

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5).

Additive twin of `CohomologyKunnethSplit`, `CohomologyKunnethNatural` and
`CohomologyKunnethMap` with the coefficients a field `K`:

```text
kunnethMapOf K : H^{n+m}(Y; K) → H^m(Y; K) → H^{n+m}(Y × S^n; K),
  (u, v) ↦ pr_Y^* u + (pr_S^* σ_n) ⌣ pr_Y^* v.
```

None of the three files uses characteristic two.  Their inputs over `K` are the sphere class
`KroneckerSphere.sphereTopClassOf`, the vanishing of a point's positive cohomology
`KroneckerContractible.cohomology_unit_isZeroOf`, and homotopy invariance
`pullEquivOfHomotopyEquivOf`; `pull`, `cup` and their algebra are already generic
(`CohomologyBasic`).  The maps `knPrY`, `knPrS`, `knSlice`, `knProdMap` carry no coefficients
and are reused.  `[CommRing K]` where no sphere or point is used, `[Field K]` otherwise.

The rest of the Künneth layer (`Hemi`, `Band`, `Step`, `Zero`, `Surj*`, `Injective`, `Decomp`)
goes through the Mayer–Vietoris sequence and is ported once the `MayerVietoris*` layer exists
over `K`.

## Main declarations

* `knSigmaOf`, `pull_knSlice_knSigmaOf` — the sphere class, killed by a slice.
* `kunneth_fst_eq_zeroOf` — a slice detects the first component.
* `kunnethMap_naturalOf` — naturality in the base.
* `kunnethMapOf`, `KunnethSecondInjectiveOf`, `kunnethInjective_of_secondOf`.
-/

open CategoryTheory Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. A slice retracts the projection -/

theorem pull_knSlice_knPrYOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (p : Sphere n) (k : ℕ) (u : Hmod K (TopCat.of Y) k) :
    pull (knSlice Y n p) k (pull (knPrY Y n) k u) = u := by
  rw [← pull_comp, knSlice_comp_prY, pull_id]

theorem pull_knPrY_injectiveOf (K : Type) [CommRing K] (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (p : Sphere n) (k : ℕ) : Function.Injective (pull (K := K) (knPrY Y n) k) := by
  intro u u' h
  have h2 := congrArg (pull (knSlice Y n p) k) h
  rwa [pull_knSlice_knPrYOf, pull_knSlice_knPrYOf] at h2

/-! ## 2. A constant map kills positive degrees -/

theorem pull_const_eq_zeroOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] {Z : Type}
    [TopologicalSpace Z] (p : Z) (k : ℕ) (hk : 1 ≤ k) (a : Hmod K (TopCat.of Z) k) :
    pull (cmap (ContinuousMap.const Y p)) k a = 0 := by
  have hfac : (cmap (ContinuousMap.const Y p) : TopCat.of Y ⟶ TopCat.of Z)
      = cmap (ContinuousMap.const Y (() : Unit)) ≫ cmap (ContinuousMap.const Unit p) := rfl
  have hz : pull (cmap (ContinuousMap.const Unit p)) k a = 0 := by
    have h := cohomology_unit_isZeroOf K k hk
    rw [ModuleCat.isZero_iff_subsingleton] at h
    exact h.elim _ 0
  rw [hfac, pull_comp, hz, pull_zero]

/-! ## 3. The sphere class and the slice -/

/-- The fundamental class of the sphere factor over `K`, pulled back to the product. -/
def knSigmaOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ) (hn : 1 ≤ n) :
    Hmod K (TopCat.of (Y × Sphere n)) n :=
  pull (knPrS Y n) n (sphereTopClassOf K n hn)

/-- **A slice kills the sphere class**, over `K`. -/
theorem pull_knSlice_knSigmaOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (hn : 1 ≤ n) (p : Sphere n) : pull (knSlice Y n p) n (knSigmaOf K Y n hn) = 0 := by
  rw [knSigmaOf, ← pull_comp, knSlice_comp_prS]
  exact pull_const_eq_zeroOf K Y p n hn _

/-- **A slice detects the first component of the Künneth map**, over `K`. -/
theorem kunneth_fst_eq_zeroOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (hn : 1 ≤ n) (p : Sphere n) (m : ℕ) (u : Hmod K (TopCat.of Y) (n + m))
    (v : Hmod K (TopCat.of Y) m)
    (h : pull (knPrY Y n) (n + m) u + cup (knSigmaOf K Y n hn) (pull (knPrY Y n) m v) = 0) :
    u = 0 := by
  have h2 := congrArg (pull (knSlice Y n p) (n + m)) h
  rw [pull_add, pull_cup, pull_knSlice_knSigmaOf, zero_cup, add_zero, pull_knSlice_knPrYOf,
    pull_zero] at h2
  exact h2

/-- The cohomology of `B × A` and of `A × B` agree over `K`, by the swap homeomorphism. -/
def prodSwapEquivOf (K : Type) [CommRing K] (A B : Type) [TopologicalSpace A]
    [TopologicalSpace B] (k : ℕ) :
    Hmod K (TopCat.of (B × A)) k ≃ₗ[K] Hmod K (TopCat.of (A × B)) k :=
  pullEquivOfHomotopyEquivOf K (Homeomorph.prodComm A B).toHomotopyEquiv k

/-! ## 4. Naturality in the base -/

theorem pull_knProdMap_knPrYOf (K : Type) [CommRing K] {Y Y' : Type} [TopologicalSpace Y]
    [TopologicalSpace Y'] (f : C(Y', Y)) (n k : ℕ) (u : Hmod K (TopCat.of Y) k) :
    pull (knProdMap f n) k (pull (knPrY Y n) k u)
      = pull (knPrY Y' n) k (pull (cmap f) k u) := by
  rw [← pull_comp, knProdMap_comp_prY, pull_comp]

theorem pull_knProdMap_knSigmaOf (K : Type) [Field K] {Y Y' : Type} [TopologicalSpace Y]
    [TopologicalSpace Y'] (f : C(Y', Y)) (n : ℕ) (hn : 1 ≤ n) :
    pull (knProdMap f n) n (knSigmaOf K Y n hn) = knSigmaOf K Y' n hn := by
  rw [knSigmaOf, knSigmaOf, ← pull_comp, knProdMap_comp_prS]

/-- **The Künneth map is natural in the base**, over `K`. -/
theorem kunnethMap_naturalOf (K : Type) [Field K] {Y Y' : Type} [TopologicalSpace Y]
    [TopologicalSpace Y'] (f : C(Y', Y)) (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (u : Hmod K (TopCat.of Y) (n + m)) (v : Hmod K (TopCat.of Y) m) :
    pull (knProdMap f n) (n + m)
        (pull (knPrY Y n) (n + m) u + cup (knSigmaOf K Y n hn) (pull (knPrY Y n) m v))
      = pull (knPrY Y' n) (n + m) (pull (cmap f) (n + m) u)
        + cup (knSigmaOf K Y' n hn) (pull (knPrY Y' n) m (pull (cmap f) m v)) := by
  rw [pull_add, pull_knProdMap_knPrYOf, pull_cup, pull_knProdMap_knSigmaOf,
    pull_knProdMap_knPrYOf]

/-! ## 5. The Künneth map and the one remaining statement -/

/-- **The Künneth map with a sphere factor over `K`**,
`(u, v) ↦ pr_Y^* u + (pr_S^* σ_n) ⌣ pr_Y^* v`. -/
def kunnethMapOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ) (hn : 1 ≤ n)
    (m : ℕ) (u : Hmod K (TopCat.of Y) (n + m)) (v : Hmod K (TopCat.of Y) m) :
    Hmod K (TopCat.of (Y × Sphere n)) (n + m) :=
  pull (knPrY Y n) (n + m) u + cup (knSigmaOf K Y n hn) (pull (knPrY Y n) m v)

theorem kunnethMapOf_eq (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (hn : 1 ≤ n) (m : ℕ) (u : Hmod K (TopCat.of Y) (n + m)) (v : Hmod K (TopCat.of Y) m) :
    kunnethMapOf K Y n hn m u v
      = pull (knPrY Y n) (n + m) u + cup (knSigmaOf K Y n hn) (pull (knPrY Y n) m v) := rfl

/-- The statement still missing for the Künneth isomorphism with a sphere factor over `K`:
cupping with the pulled-back fundamental class is injective on classes from the base.  Its
proof is the Mayer–Vietoris connecting map's `H^*(X)`-linearity over `K`. -/
def KunnethSecondInjectiveOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    Prop :=
  ∀ (hn : 1 ≤ n) (m : ℕ) (v : Hmod K (TopCat.of Y) m),
    cup (knSigmaOf K Y n hn) (pull (knPrY Y n) m v) = 0 → v = 0

/-- **Injectivity of the Künneth map over `K`**, granted the second component. -/
theorem kunnethInjective_of_secondOf (K : Type) [Field K] (Y : Type) [TopologicalSpace Y]
    (n : ℕ) (p : Sphere n) (h : KunnethSecondInjectiveOf K Y n) (hn : 1 ≤ n) (m : ℕ)
    (u : Hmod K (TopCat.of Y) (n + m)) (v : Hmod K (TopCat.of Y) m)
    (hz : kunnethMapOf K Y n hn m u v = 0) : u = 0 ∧ v = 0 := by
  have hu : u = 0 := kunneth_fst_eq_zeroOf K Y n hn p m u v hz
  refine ⟨hu, h hn m v ?_⟩
  rw [kunnethMapOf_eq, hu, pull_zero, zero_add] at hz
  exact hz

end

/-! Audited on every build. -/

#audit_axioms kunneth_fst_eq_zeroOf
#audit_axioms kunnethMap_naturalOf
#audit_axioms kunnethInjective_of_secondOf

end GroupApproximation.CharClass
