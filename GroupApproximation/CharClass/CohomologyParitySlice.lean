import GroupApproximation.CharClass.ParityEvenTransport

/-!
# The slice coordinate of a `ChernSplit`

`ChernSplit` produces its two coefficients by choice, so `alpha` is opaque as a
term and cannot be computed with.  It can, however, be *characterised*: restrict
the split along a slice of the product and the `t x` term disappears, because `t`
and `x` are pulled back from the two sphere factors and the slice meets each of
them in a point, where a constant map kills every positive degree.

So `alpha k` is the restriction of the class along the slice, and that is the
only fact about `alpha` any consumer needs.  Everything above it is then a
statement about the class itself rather than about the splitting.

## Main declarations

* `KnTwo.nSlice` — the slice `Y → (Y × S⁵) × S¹` at a chosen pair of points.
* `KnTwo.nSlice_comp_prY`, `KnTwo.nSlice_comp_prS1`, `KnTwo.nSlice_comp_prS5` —
  it sections the base projection and is constant on both sphere factors.
* `KnTwo.alpha_eq_pull_nSlice` — **the characterisation**.
* `KnTwo.ChernSliceNatural`, `KnTwo.ChernSliceValue` — the two properties of the
  class, and nothing else, that the slice identification needs.
* `KnTwo.totalH_alpha_eq_sliceClass` — **the bridge**, in the shape `hslice` has.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59

namespace GroupApproximation.CharClass

noncomputable section

namespace KnTwo

variable (Y : Type) [TopologicalSpace Y]

/-! ## 1. The slice -/

/-- **The slice** `y ↦ ((y, p₅), p₁)`, a section of the projection to the base
that meets each sphere factor in a point. -/
def nSlice (p5 : Sphere 5) (p1 : Sphere 1) : YTop Y ⟶ NTop Y :=
  knSlice Y 5 p5 ≫ knSlice (midBase Y) 1 p1

theorem nSlice_comp_prY (p5 : Sphere 5) (p1 : Sphere 1) :
    nSlice Y p5 p1 ≫ prY Y = 𝟙 (YTop Y) := by
  apply TopCat.Hom.ext
  ext x
  rfl

theorem nSlice_comp_prS1 (p5 : Sphere 5) (p1 : Sphere 1) :
    nSlice Y p5 p1 ≫ prS1 Y = cmap (ContinuousMap.const Y p1) := by
  apply TopCat.Hom.ext
  ext x
  rfl

theorem nSlice_comp_prS5 (p5 : Sphere 5) (p1 : Sphere 1) :
    nSlice Y p5 p1 ≫ prS5 Y = cmap (ContinuousMap.const Y p5) := by
  apply TopCat.Hom.ext
  ext x
  rfl

/-- The degree-one class dies on the slice: it is pulled back from the circle,
which the slice meets in a point. -/
theorem map_nSlice_tClass (p5 : Sphere 5) (p1 : Sphere 1) :
    TotalH.map (nSlice Y p5 p1)
        (Wu.tClass (prS1 Y) (sphereTopClass 1 (by omega))) = 0 := by
  rw [Wu.tClass, ← Wu.totalH_map_comp, nSlice_comp_prS1, TotalH.map_of,
    pull_const_eq_zero Y p1 1 (by omega), map_zero]

/-! ## 2. The characterisation of `alpha` -/

set_option maxHeartbeats 1000000 in
/-- **The pullback coefficient of a split is the restriction along the slice.**
No property of the class is used, and none of the splitting beyond its defining
equation, so this pins `alpha` for every `ChernSplit` at once. -/
theorem alpha_eq_pull_nSlice (p5 : Sphere 5) (p1 : Sphere 1)
    (γ : ℕ → TotalH (NTop Y)) (S : ChernSplit Y γ)
    (c : ∀ k : ℕ, Hmod2 (NTop Y) (2 * k))
    (hc : ∀ k : ℕ, γ k = TotalH.of (NTop Y) (2 * k) (c k)) (k : ℕ) :
    S.alpha k = pull (nSlice Y p5 p1) (2 * k) (c k) := by
  have hmap := congrArg (TotalH.map (nSlice Y p5 p1)) (S.split k)
  rw [map_add, map_mul, map_mul, map_nSlice_tClass, zero_mul, zero_mul, add_zero,
    ← Wu.totalH_map_comp, nSlice_comp_prY, Wu.totalH_map_id, hc k,
    TotalH.map_of] at hmap
  have hcomp := congrArg (TotalH.component (YTop Y) (2 * k)) hmap
  rw [TotalH.component_of, TotalH.component_of] at hcomp
  exact hcomp.symm

/-! ## 3. The two properties of the class, and the bridge -/

variable {ℓ : ℕ}

/-- **Naturality along the slice.**  The class restricted to the slice is the
class of the restricted family.  This is the first of the two facts about the
Chern class that the slice identification consumes. -/
def ChernSliceNatural (p5 : Sphere 5) (p1 : Sphere 1)
    (c : ∀ k : ℕ, Hmod2 (NTop Y) (2 * k))
    (v : ∀ k : ℕ, Hmod2 (YTop Y) (2 * k)) : Prop :=
  ∀ k : ℕ, pull (nSlice Y p5 p1) (2 * k) (c k) = v k

/-- **The value on the restricted family.**  Over the base the family is the
trivial-plus-hyperplane bundle, whose total class is the product of the factors,
and that product is the slice polynomial.  This is the second and last fact. -/
def ChernSliceValue (v : ∀ k : ℕ, Hmod2 (YTop Y) (2 * k))
    (gen : Fin ℓ → TotalH (YTop Y)) (dd : Fin ℓ → ℕ) : Prop :=
  ∀ q : ℕ, TotalH.of (YTop Y) (2 * q) (v q)
    = (sliceClass (Finset.univ : Finset (Fin ℓ)) gen dd).coeff q

set_option maxHeartbeats 1000000 in
/-- **The bridge.**  Over exactly those two properties, the pullback coefficient
of the split is the slice polynomial's coefficient.  Nothing else about the class
enters, and nothing about the splitting beyond its defining equation. -/
theorem totalH_alpha_eq_sliceClass (p5 : Sphere 5) (p1 : Sphere 1)
    (γ : ℕ → TotalH (NTop Y)) (S : ChernSplit Y γ)
    (c : ∀ k : ℕ, Hmod2 (NTop Y) (2 * k))
    (hc : ∀ k : ℕ, γ k = TotalH.of (NTop Y) (2 * k) (c k))
    (v : ∀ k : ℕ, Hmod2 (YTop Y) (2 * k))
    (gen : Fin ℓ → TotalH (YTop Y)) (dd : Fin ℓ → ℕ)
    (hnat : ChernSliceNatural Y p5 p1 c v)
    (hval : ChernSliceValue Y v gen dd) (q : ℕ) :
    TotalH.of (YTop Y) (2 * q) (S.alpha q)
      = (sliceClass (Finset.univ : Finset (Fin ℓ)) gen dd).coeff q := by
  rw [alpha_eq_pull_nSlice Y p5 p1 γ S c hc q, hnat q]
  exact hval q

end KnTwo

end

end GroupApproximation.CharClass
