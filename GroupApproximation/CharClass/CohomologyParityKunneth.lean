import GroupApproximation.CharClass.CohomologyKunnethInjective
import GroupApproximation.CharClass.SqDataInstance

/-!
# Künneth for the two sphere factors of the mapping-torus base

`cc-wu`'s `htx_inj` field asks that the `t x`-coordinate of a class of
`H^*(S¹ × S⁵ × Y)` be well defined: if `ι u + t x ι v = 0` then `v = 0`.  That is
Künneth injectivity for **two** sphere factors, and it comes from the one-factor
statement applied twice, peeling one sphere at a time.

The base is written left-nested as `(Y × S⁵) × S¹`, because `KnHemi`'s Künneth
lemma always puts the new sphere on the right.  The circle is peeled first: a
slice of the circle factor kills `t`, which forces the `ι u` summand to vanish,
and what is left is one application of the one-factor lemma over the base
`Y × S⁵`, then a second over `Y`.

The ring-level statement is the degreewise one read off componentwise.  The
component of a product `of i w * z` at `i + m` is `w ⌣ (component m z)`, which is
`component_of_mul` below; with `cc-wu`'s `totalH_component_map` for the pullback,
the field reduces to `KnTwo.tx_inj_degree` at each degree.

## Main declarations

* `KnTwo.torusBase`, `KnTwo.prY`, `KnTwo.prS1`, `KnTwo.prS5` — the model and its
  three projections.
* `KnTwo.tx_inj_degree` — the degreewise statement.
* `KnTwo.htx_inj` — `cc-wu`'s field.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 0. The component of a product -/

/-- **The component of `of i w * z` at `i + m` is `w ⌣ (component m z)`.** -/
theorem component_of_mul {X : TopCat.{0}} (i m : ℕ) (w : TotalPiece X i) (z : TotalH X) :
    TotalH.component X (i + m) (TotalH.of X i w * z) = cup w (TotalH.component X m z) := by
  induction z using DirectSum.induction_on with
  | zero => rw [mul_zero, map_zero, map_zero, cup_zero]
  | of j c =>
    show TotalH.component X (i + m) (TotalH.of X i w * TotalH.of X j c)
      = cup w (TotalH.component X m (TotalH.of X j c))
    rw [← TotalH.of_mul]
    rcases eq_or_ne j m with rfl | hjm
    · rw [TotalH.component_of, TotalH.component_of]
    · rw [Wu.component_of_ne (show i + m ≠ i + j by omega), Wu.component_of_ne hjm.symm,
        cup_zero]
  | add z₁ z₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, cup_add_right]

namespace KnTwo

variable (Y : Type) [TopologicalSpace Y]

/-! ## 1. The model and its projections -/

/-- The intermediate base `Y × S⁵`. -/
abbrev midBase : Type := Y × Sphere 5

/-- The mapping-torus base, left-nested as `(Y × S⁵) × S¹`. -/
abbrev torusBase : Type := midBase Y × Sphere 1

/-- The mapping-torus base as an object of `TopCat`. -/
abbrev NTop : TopCat.{0} := TopCat.of (torusBase Y)

/-- The fibre base as an object of `TopCat`. -/
abbrev YTop : TopCat.{0} := TopCat.of Y

/-- The projection to `Y`. -/
def prY : NTop Y ⟶ YTop Y := knPrY (midBase Y) 1 ≫ knPrY Y 5

/-- The projection to the circle factor. -/
def prS1 : NTop Y ⟶ TopCat.of (Sphere 1) := knPrS (midBase Y) 1

/-- The projection to the `S⁵` factor. -/
def prS5 : NTop Y ⟶ TopCat.of (Sphere 5) := knPrY (midBase Y) 1 ≫ knPrS Y 5

/-- The degree-one generator on the base. -/
def sig1 : Hmod2 (NTop Y) 1 := knSigma (midBase Y) 1 (by omega)

/-- The degree-five generator on the base. -/
def sig5 : Hmod2 (NTop Y) 5 := pull (knPrY (midBase Y) 1) 5 (knSigma Y 5 (by omega))

theorem pull_prS1 : pull (prS1 Y) 1 (sphereTopClass 1 (by omega)) = sig1 Y := rfl

theorem pull_prS5 : pull (prS5 Y) 5 (sphereTopClass 5 (by omega)) = sig5 Y := by
  rw [prS5, pull_comp]
  rfl

/-! ## 2. The degreewise statement -/

set_option maxHeartbeats 1000000 in
/-- **Künneth injectivity for the two sphere factors, in a single degree.** -/
theorem tx_inj_degree (m : ℕ) (uu : Hmod2 (YTop Y) (1 + 5 + m))
    (vv : Hmod2 (YTop Y) m)
    (h : pull (prY Y) (1 + 5 + m) uu
      + cup (cup (sig1 Y) (sig5 Y)) (pull (prY Y) m vv) = 0) : vv = 0 := by
  have hslice : ∀ (k : ℕ) (a : Hmod2 (YTop Y) k),
      pull (knSlice (midBase Y) 1 (northPole 0)) k (pull (prY Y) k a)
        = pull (knPrY Y 5) k a := by
    intro k a
    rw [prY, pull_comp, pull_knSlice_knPrY]
  have hsig1 : pull (knSlice (midBase Y) 1 (northPole 0)) 1 (sig1 Y) = 0 :=
    pull_knSlice_knSigma (midBase Y) 1 (by omega) (northPole 0)
  -- the circle slice kills the `t x` term, so the first summand vanishes
  have hU : pull (knPrY Y 5) (1 + 5 + m) uu = 0 := by
    have hh := congrArg (pull (knSlice (midBase Y) 1 (northPole 0)) (1 + 5 + m)) h
    rw [pull_add, pull_zero, hslice, pull_cup, pull_cup, hsig1, zero_cup, zero_cup,
      add_zero] at hh
    exact hh
  have h2 : cup (cup (sig1 Y) (sig5 Y)) (pull (prY Y) m vv) = 0 := by
    have hz : pull (prY Y) (1 + 5 + m) uu = 0 := by
      rw [prY, pull_comp, hU, pull_zero]
    rwa [hz, zero_add] at h
  -- reassociate and peel the circle factor
  have h3 : cup (sig1 Y) (cup (sig5 Y) (pull (prY Y) m vv)) = 0 := by
    rw [← cup_assoc, h2]
    exact KnHemi.cohCast_zero _
  have h4 : cup (sig5 Y) (pull (prY Y) m vv)
      = pull (knPrY (midBase Y) 1) (5 + m)
          (cup (knSigma Y 5 (by omega)) (pull (knPrY Y 5) m vv)) := by
    rw [pull_cup, sig5, prY, pull_comp]
  have h5 : cup (knSigma Y 5 (by omega)) (pull (knPrY Y 5) m vv) = 0 := by
    refine KnHemi.kunnethSecondInjective (midBase Y) 1 (by omega) (5 + m) _ ?_
    rw [← h4]
    exact h3
  exact KnHemi.kunnethSecondInjective Y 5 (by omega) m vv h5

/-! ## 3. `cc-wu`'s field -/

/-- The product of the two sphere generators, as an element of the total ring. -/
theorem tClass_mul_xClass :
    Wu.tClass (prS1 Y) (sphereTopClass 1 (by omega))
        * Wu.xClass (prS5 Y) (sphereTopClass 5 (by omega))
      = TotalH.of (NTop Y) (1 + 5) (cup (sig1 Y) (sig5 Y)) := by
  rw [Wu.tClass, Wu.xClass, TotalH.map_of, TotalH.map_of, TotalH.of_mul, pull_prS1,
    pull_prS5]

set_option maxHeartbeats 1000000 in
/-- **`cc-wu`'s `htx_inj` field.**  The `t x`-coordinate of a class on the
mapping-torus base is well defined. -/
theorem htx_inj (u v : TotalH (YTop Y))
    (h : TotalH.map (prY Y) u
      + Wu.tClass (prS1 Y) (sphereTopClass 1 (by omega))
        * Wu.xClass (prS5 Y) (sphereTopClass 5 (by omega))
        * TotalH.map (prY Y) v = 0) : v = 0 := by
  refine DirectSum.ext _ (fun m => ?_)
  show TotalH.component (YTop Y) m v = TotalH.component (YTop Y) m (0 : TotalH (YTop Y))
  rw [map_zero]
  have hc := congrArg (TotalH.component (NTop Y) (1 + 5 + m)) h
  rw [map_add, map_zero, Wu.totalH_component_map, tClass_mul_xClass, component_of_mul,
    Wu.totalH_component_map] at hc
  exact tx_inj_degree Y m (TotalH.component (YTop Y) (1 + 5 + m) u)
    (TotalH.component (YTop Y) m v) hc

end KnTwo

end

end GroupApproximation.CharClass
