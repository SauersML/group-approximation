import GroupApproximation.Analysis.UniformTracialSequenceCompletion
import GroupApproximation.Analysis.CuntzPedersenCoronaObstruction

/-!
# The uniform two-null ideal `J` and the sequence algebra `ℂ1 + J`

`Analysis/UniformTracialSequenceCompletion` records the *truncation* half of
the identification `M = ℂ1 + J` for an abstract coordinate gauge whose only
recorded properties are `q 0 = 0`, `0 ≤ q` and `q ≤ ‖·‖`.  Those three
properties are not enough to know that the two-null sequences form an ideal,
nor that the scalar in a decomposition `x = λ1 + j` is unique.

This file supplies the missing structure.  A `TracialTwoGauge` carries the
data of a `UniformTwoGauge` — and maps to one by `toUniformTwoGauge`, so every
landed theorem applies verbatim — together with

* subadditivity,
* the bimodule bounds `q (a x) ≤ ‖a‖ q x` and `q (x a) ≤ q x ‖a‖`,
* invariance under the involution, and
* normalization, `q 1 = 1`.

These are exactly the properties of the audit's coordinate two-norm
`‖x‖_{2,s} = sup_{y ∈ X_s} tr_{s+1}(x(y)^* x(y))^{1/2}` that Section 4 uses:
subadditivity and the bimodule bounds are the Minkowski and Cauchy--Schwarz
estimates for a tracial state, involution invariance is traciality, and
normalization says the coordinate traces are states.

With them:

* `twoNullIdeal` is the audit's `J` of (A7), a norm-closed, star-stable,
  two-sided ideal of the bounded product containing the `c₀` sum, and strictly
  containing it as soon as a `TraciallyNullObstruction` is available;
* `scalarPlusJ` is the audit's `M = ℂ1 + J` of (A8), a star subalgebra of the
  bounded product which is norm closed, and on which the scalar coefficient is
  unique and contractive.

The normalization field `one_eq` is load-bearing and not decorative: the
rescaled gauge `q n x = ‖x‖ / (n+1)` satisfies every *other* field, and for it
`J` is the whole bounded product and the scalar in a decomposition is not
unique.  Dropping `one_eq` therefore collapses `ℂ1 + J` to `∏_s D_s`.

Nothing here is vacuous: `normTracialTwoGauge` shows that the operator norm
itself is a `TracialTwoGauge` satisfying the audit's coordinatewise finite-rank
comparison, and for the constant family `D_s = ℂ` — whose unique tracial state
is the identity — that gauge *is* the uniform tracial two-norm, so the model is
faithful rather than degenerate.
-/

namespace GroupApproximation
namespace UniformTracialTwoNullIdeal

open Filter PolarLiftingGeneralCStar
open UniformTracialSequenceCompletion CuntzPedersenCoronaObstruction

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)]

/-! ## Coordinate two-gauges with the ideal estimates -/

/-- A coordinate uniform two-gauge together with the estimates which make the
two-null sequences an ideal and the scalar part of `ℂ1 + J` unique.

For the audit's blocks the gauge is
`q s x = sup_{y ∈ X_s} tr_{s+1}(x(y)^* x(y))^{1/2}`; `add_le` is Minkowski,
`mul_left_le` and `mul_right_le` are the two Cauchy--Schwarz bounds,
`star_eq` is traciality and `one_eq` says the fibre traces are states.

The first four fields duplicate `UniformTwoGauge`; `toUniformTwoGauge` is the
forgetful map, so this is a strengthening of the landed structure and not a
parallel notion. -/
structure TracialTwoGauge (D : ℕ → Type u) [∀ n, CStarAlgebra (D n)] where
  /-- The coordinate gauge. -/
  q : ∀ n, D n → ℝ
  /-- The gauge vanishes at zero. -/
  zero : ∀ n, q n 0 = 0
  /-- The gauge is nonnegative. -/
  nonneg : ∀ (n : ℕ) (x : D n), 0 ≤ q n x
  /-- The gauge is dominated by the operator norm. -/
  le_norm : ∀ (n : ℕ) (x : D n), q n x ≤ ‖x‖
  /-- Coordinatewise subadditivity. -/
  add_le : ∀ (n : ℕ) (x y : D n), q n (x + y) ≤ q n x + q n y
  /-- Left bimodule bound `q (a x) ≤ ‖a‖ q x`. -/
  mul_left_le : ∀ (n : ℕ) (a x : D n), q n (a * x) ≤ ‖a‖ * q n x
  /-- Right bimodule bound `q (x a) ≤ q x ‖a‖`. -/
  mul_right_le : ∀ (n : ℕ) (x a : D n), q n (x * a) ≤ q n x * ‖a‖
  /-- Traciality makes the gauge invariant under the involution. -/
  star_eq : ∀ (n : ℕ) (x : D n), q n (star x) = q n x
  /-- The gauge is normalized at the unit. -/
  one_eq : ∀ n : ℕ, q n (1 : D n) = 1

namespace TracialTwoGauge

variable (G : TracialTwoGauge D)

/-- Forget the ideal estimates, landing in the structure used by
`Analysis/UniformTracialSequenceCompletion`.  All the landed truncation
theorems are applied through this map. -/
def toUniformTwoGauge : UniformTwoGauge D where
  q := G.q
  zero := G.zero
  nonneg := G.nonneg
  le_norm := G.le_norm

@[simp] theorem toUniformTwoGauge_q : G.toUniformTwoGauge.q = G.q := rfl

/-- Scalar multiples are contracted by the modulus of the scalar. -/
theorem smul_le (n : ℕ) (c : ℂ) (x : D n) :
    G.q n (c • x) ≤ ‖c‖ * G.q n x := by
  have hsmul : c • x = algebraMap ℂ (D n) c * x := Algebra.smul_def c x
  have h := G.mul_left_le n (algebraMap ℂ (D n) c) x
  rw [hsmul]
  exact h.trans_eq (by rw [norm_algebraMap'])

/-- The gauge is absolutely homogeneous. -/
theorem smul_eq (n : ℕ) (c : ℂ) (x : D n) :
    G.q n (c • x) = ‖c‖ * G.q n x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [G.zero]
  · refine le_antisymm (G.smul_le n c x) ?_
    have hcpos : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
    have h := G.smul_le n c⁻¹ (c • x)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, norm_inv] at h
    calc ‖c‖ * G.q n x ≤ ‖c‖ * (‖c‖⁻¹ * G.q n (c • x)) :=
          mul_le_mul_of_nonneg_left h hcpos.le
      _ = G.q n (c • x) := by
          rw [← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]

/-- The gauge is invariant under negation. -/
theorem neg_eq (n : ℕ) (x : D n) : G.q n (-x) = G.q n x := by
  have key : ∀ y : D n, G.q n (-y) ≤ G.q n y := by
    intro y
    have h := G.mul_left_le n (-1 : D n) y
    rwa [neg_one_mul, norm_neg, norm_one, one_mul] at h
  exact le_antisymm (key x) (by simpa using key (-x))

/-- The triangle inequality in the form used to split off an approximant. -/
theorem le_add_sub (n : ℕ) (x y : D n) :
    G.q n x ≤ G.q n (x - y) + G.q n y := by
  have h := G.add_le n (x - y) y
  rwa [sub_add_cancel] at h

/-- The three-point triangle inequality for differences. -/
theorem sub_le_sub_add_sub (n : ℕ) (x y z : D n) :
    G.q n (x - z) ≤ G.q n (x - y) + G.q n (y - z) := by
  have h := G.add_le n (x - y) (y - z)
  rwa [sub_add_sub_cancel] at h

/-- Subadditivity for differences. -/
theorem sub_le_add (n : ℕ) (x y : D n) :
    G.q n (x - y) ≤ G.q n x + G.q n y := by
  have h := G.add_le n x (-y)
  rw [G.neg_eq] at h
  rwa [← sub_eq_add_neg] at h

/-- Differences are measured symmetrically. -/
theorem sub_comm_eq (n : ℕ) (x y : D n) :
    G.q n (x - y) = G.q n (y - x) := by
  rw [← G.neg_eq n (x - y), neg_sub]

/-- The gauge of a scalar is the modulus of the scalar.  This is the
normalization which makes the scalar part of `ℂ1 + J` unique. -/
theorem q_algebraMap (n : ℕ) (c : ℂ) :
    G.q n (algebraMap ℂ (D n) c) = ‖c‖ := by
  rw [Algebra.algebraMap_eq_smul_one, G.smul_eq, G.one_eq, mul_one]

end TracialTwoGauge

/-! ## The operator-norm model -/

/-- The operator norm itself is a `TracialTwoGauge`.  For the constant family
`D_s = ℂ` the unique tracial state is the identity, so this *is* the uniform
tracial two-gauge; the model test is therefore faithful, not degenerate. -/
def normTracialTwoGauge (D : ℕ → Type u) [∀ n, CStarAlgebra (D n)]
    [∀ n, Nontrivial (D n)] : TracialTwoGauge D where
  q := fun _ x ↦ ‖x‖
  zero := fun _ ↦ norm_zero
  nonneg := fun _ x ↦ norm_nonneg x
  le_norm := fun _ _ ↦ le_rfl
  add_le := fun _ x y ↦ norm_add_le x y
  mul_left_le := fun _ a x ↦ norm_mul_le a x
  mul_right_le := fun _ x a ↦ norm_mul_le x a
  star_eq := fun _ x ↦ norm_star x
  one_eq := fun _ ↦ norm_one

@[simp] theorem normTracialTwoGauge_q (n : ℕ) (x : D n) :
    (normTracialTwoGauge D).q n x = ‖x‖ := rfl

/-- The audit's coordinatewise finite-rank comparison, with the constant
exposed: on the `s`-th block the operator norm is at most `r s` times the
two-gauge.  For blocks with fibre `M_{s+1}` and normalized fibre trace the
Hilbert--Schmidt comparison gives `r s = sqrt (s+1)`. -/
def IsCoordinateNormComparison (G : TracialTwoGauge D) (r : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : D n), ‖x‖ ≤ r n * G.q n x

/-- The audit's constant `sqrt (s+1)`. -/
def sqrtSuccBound : ℕ → ℝ := fun n ↦ Real.sqrt (n + 1)

theorem one_le_sqrtSuccBound (n : ℕ) : 1 ≤ sqrtSuccBound n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h : Real.sqrt 1 ≤ Real.sqrt ((n : ℝ) + 1) := by
    apply Real.sqrt_le_sqrt
    linarith
  rwa [Real.sqrt_one] at h

/-- The operator-norm model satisfies the finite-rank comparison with the
audit's own constant, so that hypothesis is consistent with all the others. -/
theorem normTracialTwoGauge_isCoordinateNormComparison :
    IsCoordinateNormComparison (normTracialTwoGauge D) sqrtSuccBound := by
  intro n x
  rw [normTracialTwoGauge_q]
  calc ‖x‖ = 1 * ‖x‖ := (one_mul _).symm
    _ ≤ sqrtSuccBound n * ‖x‖ :=
        mul_le_mul_of_nonneg_right (one_le_sqrtSuccBound n) (norm_nonneg x)

/-! ## The ideal `J` -/

/-- `J` of the audit's (A7): the bounded coordinate sequences whose coordinate
two-gauges tend to zero.  The membership predicate is `IsUniformTwoNull`,
already used by `Analysis/CuntzPedersenCoronaObstruction`; this packages it as
an ideal of the bounded product. -/
def twoNullIdeal (G : TracialTwoGauge D) : Ideal (BoundedCStarSequence D) where
  carrier := {x | IsUniformTwoNull G.q x}
  zero_mem' := by
    show Tendsto (fun n ↦ G.q n ((0 : BoundedCStarSequence D) n)) atTop (nhds 0)
    have hzero : (fun n ↦ G.q n ((0 : BoundedCStarSequence D) n))
        = fun _ : ℕ ↦ (0 : ℝ) := by
      funext n
      exact G.zero n
    rw [hzero]
    exact tendsto_const_nhds
  add_mem' := by
    intro x y hx hy
    have hx' : Tendsto (fun n ↦ G.q n (x n)) atTop (nhds 0) := hx
    have hy' : Tendsto (fun n ↦ G.q n (y n)) atTop (nhds 0) := hy
    show Tendsto (fun n ↦ G.q n ((x + y) n)) atTop (nhds 0)
    have hsum : Tendsto (fun n ↦ G.q n (x n) + G.q n (y n)) atTop (nhds 0) := by
      simpa using hx'.add hy'
    refine squeeze_zero' (Eventually.of_forall fun n ↦ G.nonneg n _)
      (Eventually.of_forall fun n ↦ ?_) hsum
    exact G.add_le n (x n) (y n)
  smul_mem' := by
    intro c x hx
    have hx' : Tendsto (fun n ↦ G.q n (x n)) atTop (nhds 0) := hx
    show Tendsto (fun n ↦ G.q n ((c • x) n)) atTop (nhds 0)
    have hbound : Tendsto (fun n ↦ ‖c‖ * G.q n (x n)) atTop (nhds 0) := by
      simpa using hx'.const_mul ‖c‖
    refine squeeze_zero' (Eventually.of_forall fun n ↦ G.nonneg n _)
      (Eventually.of_forall fun n ↦ ?_) hbound
    calc G.q n ((c • x) n) ≤ ‖c n‖ * G.q n (x n) := G.mul_left_le n (c n) (x n)
      _ ≤ ‖c‖ * G.q n (x n) :=
          mul_le_mul_of_nonneg_right
            (boundedCStarSequence_coord_norm_le D c n) (G.nonneg n _)

theorem mem_twoNullIdeal_iff {G : TracialTwoGauge D}
    {x : BoundedCStarSequence D} :
    x ∈ twoNullIdeal G ↔ Tendsto (fun n ↦ G.q n (x n)) atTop (nhds 0) :=
  Iff.rfl

/-- `J` is a right ideal as well, by the right-hand bimodule bound. -/
instance twoNullIdeal_isTwoSided (G : TracialTwoGauge D) :
    (twoNullIdeal G).IsTwoSided where
  mul_mem_of_left := by
    intro x y hx
    have hx' : Tendsto (fun n ↦ G.q n (x n)) atTop (nhds 0) := hx
    show Tendsto (fun n ↦ G.q n ((x * y) n)) atTop (nhds 0)
    have hbound : Tendsto (fun n ↦ G.q n (x n) * ‖y‖) atTop (nhds 0) := by
      simpa using hx'.mul_const ‖y‖
    refine squeeze_zero' (Eventually.of_forall fun n ↦ G.nonneg n _)
      (Eventually.of_forall fun n ↦ ?_) hbound
    calc G.q n ((x * y) n) ≤ G.q n (x n) * ‖y n‖ := G.mul_right_le n (x n) (y n)
      _ ≤ G.q n (x n) * ‖y‖ :=
          mul_le_mul_of_nonneg_left
            (boundedCStarSequence_coord_norm_le D y n) (G.nonneg n _)

/-- `J` is stable under the involution, by traciality of the gauge. -/
theorem twoNullIdeal_star_mem {G : TracialTwoGauge D}
    {x : BoundedCStarSequence D} (hx : x ∈ twoNullIdeal G) :
    star x ∈ twoNullIdeal G := by
  have hx' : Tendsto (fun n ↦ G.q n (x n)) atTop (nhds 0) := hx
  show Tendsto (fun n ↦ G.q n ((star x) n)) atTop (nhds 0)
  have hfun : (fun n ↦ G.q n ((star x) n)) = fun n ↦ G.q n (x n) := by
    funext n
    rw [lp.star_apply]
    exact G.star_eq n (x n)
  rw [hfun]
  exact hx'

/-- The `c₀` sum `B = ⊕_s D_s` is contained in `J`, because the gauge is
dominated by the operator norm. -/
theorem nullCStarSequenceIdeal_le_twoNullIdeal (G : TracialTwoGauge D) :
    nullCStarSequenceIdeal D atTop ≤ twoNullIdeal G := by
  intro x hx
  have hx' : Tendsto (fun n ↦ ‖x n‖) atTop (nhds 0) := hx
  show Tendsto (fun n ↦ G.q n (x n)) atTop (nhds 0)
  exact squeeze_zero' (Eventually.of_forall fun n ↦ G.nonneg n _)
    (Eventually.of_forall fun n ↦ G.le_norm n _) hx'

/-- `J` is norm closed in the bounded product. -/
theorem isClosed_twoNullIdeal (G : TracialTwoGauge D) :
    IsClosed (twoNullIdeal G : Set (BoundedCStarSequence D)) := by
  apply IsSeqClosed.isClosed
  intro a x ha hax
  show Tendsto (fun n ↦ G.q n (x n)) atTop (nhds 0)
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  obtain ⟨k, hk⟩ :=
    ((Metric.tendsto_nhds.mp hax) (ε / 2) (half_pos hε)).exists
  have hak : Tendsto (fun n ↦ G.q n (a k n)) atTop (nhds 0) := ha k
  have htail : ∀ᶠ n in atTop, G.q n (a k n) < ε / 2 :=
    ((Metric.tendsto_nhds.mp hak) (ε / 2) (half_pos hε)).mono fun n hn ↦ by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (G.nonneg n _)] using hn
  have hnorm : ‖x - a k‖ < ε / 2 := by
    have h := hk
    rwa [dist_comm, dist_eq_norm] at h
  filter_upwards [htail] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (G.nonneg n _)]
  have hsplit : G.q n (x n) ≤ G.q n (x n - a k n) + G.q n (a k n) :=
    G.le_add_sub n (x n) (a k n)
  have hcoord : G.q n (x n - a k n) ≤ ‖x - a k‖ := by
    calc G.q n (x n - a k n) ≤ ‖x n - a k n‖ := G.le_norm n _
      _ = ‖(x - a k) n‖ := rfl
      _ ≤ ‖x - a k‖ := boundedCStarSequence_coord_norm_le D (x - a k) n
  linarith

/-- With the operator norm as gauge, `J` is exactly the `c₀` ideal.  This
records that the abstract hypotheses have a model in which every construction
below specializes to the classical one. -/
theorem twoNullIdeal_normTracialTwoGauge :
    twoNullIdeal (normTracialTwoGauge D) = nullCStarSequenceIdeal D atTop := by
  ext x
  exact Iff.rfl

/-- The obstructing sequence of a `TraciallyNullObstruction` lies in `J` and
not in the `c₀` ideal, as soon as the recorded coordinate two-size is the
gauge.  This is the audit's `h ∈ J \ B` from (A1) and (A10): `J` is strictly
larger than `⊕_s D_s`. -/
theorem obstruction_mem_twoNullIdeal_not_mem_nullIdeal
    (G : TracialTwoGauge D) (B : TraciallyNullObstruction D)
    (hq : B.twoSize = G.q) :
    B.toBlockObstruction.sequence ∈ twoNullIdeal G ∧
      B.toBlockObstruction.sequence ∉ nullCStarSequenceIdeal D atTop := by
  refine ⟨?_, B.sequence_not_isNullCStarSequence⟩
  have h := B.sequence_isUniformTwoNull
  rw [hq] at h
  exact h

/-! ## The algebra `M = ℂ1 + J` -/

/-- The audit's `M = ℂ1 + J` of (A8), as a literal set of bounded sequences. -/
def scalarPlusJ (G : TracialTwoGauge D) : Set (BoundedCStarSequence D) :=
  {x | ∃ c : ℂ, ∃ j ∈ twoNullIdeal G,
    x = algebraMap ℂ (BoundedCStarSequence D) c + j}

theorem mem_scalarPlusJ_iff {G : TracialTwoGauge D}
    {x : BoundedCStarSequence D} :
    x ∈ scalarPlusJ G ↔ ∃ c : ℂ, ∃ j ∈ twoNullIdeal G,
      x = algebraMap ℂ (BoundedCStarSequence D) c + j := Iff.rfl

theorem mem_scalarPlusJ_iff_sub {G : TracialTwoGauge D}
    {x : BoundedCStarSequence D} :
    x ∈ scalarPlusJ G ↔
      ∃ c : ℂ, x - algebraMap ℂ (BoundedCStarSequence D) c ∈ twoNullIdeal G := by
  constructor
  · rintro ⟨c, j, hj, rfl⟩
    refine ⟨c, ?_⟩
    have hcancel : algebraMap ℂ (BoundedCStarSequence D) c + j
        - algebraMap ℂ (BoundedCStarSequence D) c = j := by abel
    rw [hcancel]
    exact hj
  · rintro ⟨c, hc⟩
    exact ⟨c, x - algebraMap ℂ (BoundedCStarSequence D) c, hc, by abel⟩

/-- `ℂ1 + J` is exactly the set already shown in
`Analysis/UniformTracialSequenceCompletion` to be uniformly two-approximable
by scalar truncations.  This is the bridge which turns the landed truncation
theorems into statements about the ideal `J`. -/
theorem scalarPlusJ_eq_scalarPlusTwoNull (G : TracialTwoGauge D) :
    scalarPlusJ G = scalarPlusTwoNull G.toUniformTwoGauge := by
  ext x
  rw [mem_scalarPlusJ_iff_sub]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc⟩

/-- The scalar coefficient functional on `ℂ1 + J` is contractive: no element
of `J` can cancel a scalar.  This is what forces `ℂ1 + J` to be closed. -/
theorem norm_le_norm_algebraMap_add (G : TracialTwoGauge D) (c : ℂ)
    {j : BoundedCStarSequence D} (hj : j ∈ twoNullIdeal G) :
    ‖c‖ ≤ ‖algebraMap ℂ (BoundedCStarSequence D) c + j‖ := by
  have hj' : Tendsto (fun n ↦ G.q n (j n)) atTop (nhds 0) := hj
  have hstep : ∀ n : ℕ, ‖c‖
      ≤ ‖algebraMap ℂ (BoundedCStarSequence D) c + j‖ + G.q n (j n) := by
    intro n
    have hxn : (algebraMap ℂ (BoundedCStarSequence D) c + j) n
        = algebraMap ℂ (D n) c + j n := rfl
    have h1 : G.q n (algebraMap ℂ (D n) c)
        ≤ G.q n ((algebraMap ℂ (BoundedCStarSequence D) c + j) n)
          + G.q n (j n) := by
      rw [hxn]
      have h := G.sub_le_add n (algebraMap ℂ (D n) c + j n) (j n)
      rwa [add_sub_cancel_right] at h
    have h2 : G.q n ((algebraMap ℂ (BoundedCStarSequence D) c + j) n)
        ≤ ‖algebraMap ℂ (BoundedCStarSequence D) c + j‖ :=
      (G.le_norm n _).trans
        (boundedCStarSequence_coord_norm_le D
          (algebraMap ℂ (BoundedCStarSequence D) c + j) n)
    have h3 : G.q n (algebraMap ℂ (D n) c) = ‖c‖ := G.q_algebraMap n c
    linarith
  have hconst : Tendsto
      (fun _ : ℕ ↦ ‖algebraMap ℂ (BoundedCStarSequence D) c + j‖) atTop
      (nhds ‖algebraMap ℂ (BoundedCStarSequence D) c + j‖) :=
    tendsto_const_nhds
  have hlim : Tendsto
      (fun n ↦ ‖algebraMap ℂ (BoundedCStarSequence D) c + j‖ + G.q n (j n))
      atTop (nhds ‖algebraMap ℂ (BoundedCStarSequence D) c + j‖) := by
    simpa using hconst.add hj'
  exact ge_of_tendsto' hlim hstep

/-- The scalar in a decomposition `x = λ1 + j` with `j ∈ J` is unique. -/
theorem scalar_unique (G : TracialTwoGauge D) {c c' : ℂ}
    {j j' : BoundedCStarSequence D} (hj : j ∈ twoNullIdeal G)
    (hj' : j' ∈ twoNullIdeal G)
    (h : algebraMap ℂ (BoundedCStarSequence D) c + j
      = algebraMap ℂ (BoundedCStarSequence D) c' + j') :
    c = c' := by
  have hk : j - j' ∈ twoNullIdeal G := sub_mem hj hj'
  have hsum : algebraMap ℂ (BoundedCStarSequence D) (c - c') + (j - j') = 0 := by
    rw [map_sub, sub_add_sub_comm, h, sub_self]
  have hle := norm_le_norm_algebraMap_add G (c - c') hk
  rw [hsum, norm_zero] at hle
  have hzero : ‖c - c'‖ = 0 := le_antisymm hle (norm_nonneg _)
  exact eq_of_sub_eq_zero (norm_eq_zero.mp hzero)

/-- `M = ℂ1 + J` as a star subalgebra of the bounded product. -/
def scalarPlusJSubalgebra (G : TracialTwoGauge D) :
    StarSubalgebra ℂ (BoundedCStarSequence D) where
  carrier := scalarPlusJ G
  zero_mem' := ⟨0, 0, Ideal.zero_mem _, by simp⟩
  one_mem' := ⟨1, 0, Ideal.zero_mem _, by simp⟩
  add_mem' := by
    rintro x y ⟨c, j, hj, rfl⟩ ⟨c', j', hj', rfl⟩
    refine ⟨c + c', j + j', Ideal.add_mem _ hj hj', ?_⟩
    rw [map_add]
    abel
  mul_mem' := by
    rintro x y ⟨c, j, hj, rfl⟩ ⟨c', j', hj', rfl⟩
    refine ⟨c * c',
      algebraMap ℂ (BoundedCStarSequence D) c * j'
        + j * algebraMap ℂ (BoundedCStarSequence D) c' + j * j', ?_, ?_⟩
    · exact Ideal.add_mem _
        (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hj')
          (Ideal.mul_mem_right _ _ hj))
        (Ideal.mul_mem_left _ _ hj')
    · rw [map_mul, add_mul, mul_add, mul_add]
      abel
  algebraMap_mem' := fun c ↦ ⟨c, 0, Ideal.zero_mem _, by simp⟩
  star_mem' := by
    rintro x ⟨c, j, hj, rfl⟩
    refine ⟨star c, star j, twoNullIdeal_star_mem hj, ?_⟩
    rw [star_add, ← algebraMap_star_comm]

theorem mem_scalarPlusJSubalgebra {G : TracialTwoGauge D}
    {x : BoundedCStarSequence D} :
    x ∈ scalarPlusJSubalgebra G ↔ x ∈ scalarPlusJ G := Iff.rfl

theorem coe_scalarPlusJSubalgebra (G : TracialTwoGauge D) :
    (scalarPlusJSubalgebra G : Set (BoundedCStarSequence D)) = scalarPlusJ G :=
  Set.ext fun _ ↦ mem_scalarPlusJSubalgebra

/-- `ℂ1 + J` is norm closed: the scalar coefficients of a convergent sequence
of its elements are Cauchy by contractivity, and `J` is closed. -/
theorem isClosed_scalarPlusJ (G : TracialTwoGauge D) :
    IsClosed (scalarPlusJ G) := by
  apply IsSeqClosed.isClosed
  intro a x ha hax
  have ha' : ∀ m : ℕ, ∃ d : ℂ, ∃ i ∈ twoNullIdeal G,
      a m = algebraMap ℂ (BoundedCStarSequence D) d + i := ha
  choose c j hj hdec using ha'
  have hcauchy : CauchySeq c := by
    refine Metric.cauchySeq_iff.2 ?_
    intro ε hε
    obtain ⟨N, hN⟩ :=
      Metric.cauchySeq_iff.mp hax.cauchySeq (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm k hk ↦ ?_⟩
    have hle := norm_le_norm_algebraMap_add G (c m - c k) (sub_mem (hj m) (hj k))
    have heq : algebraMap ℂ (BoundedCStarSequence D) (c m - c k) + (j m - j k)
        = a m - a k := by
      rw [map_sub, sub_add_sub_comm, ← hdec m, ← hdec k]
    rw [heq] at hle
    calc dist (c m) (c k) = ‖c m - c k‖ := by rw [dist_eq_norm]
      _ ≤ ‖a m - a k‖ := hle
      _ = dist (a m) (a k) := by rw [dist_eq_norm]
      _ < ε / 2 := hN m hm k hk
      _ < ε := by linarith
  obtain ⟨c0, hc0⟩ := cauchySeq_tendsto_of_complete hcauchy
  show ∃ d : ℂ, ∃ i ∈ twoNullIdeal G,
    x = algebraMap ℂ (BoundedCStarSequence D) d + i
  refine ⟨c0, x - algebraMap ℂ (BoundedCStarSequence D) c0, ?_, by abel⟩
  have hAc : Tendsto (fun m ↦ algebraMap ℂ (BoundedCStarSequence D) (c m))
      atTop (nhds (algebraMap ℂ (BoundedCStarSequence D) c0)) :=
    ((continuous_algebraMap ℂ (BoundedCStarSequence D)).tendsto c0).comp hc0
  have hfun : j = fun m ↦ a m - algebraMap ℂ (BoundedCStarSequence D) (c m) := by
    funext m
    rw [hdec m]
    abel
  have hlim : Tendsto j atTop
      (nhds (x - algebraMap ℂ (BoundedCStarSequence D) c0)) := by
    rw [hfun]
    exact hax.sub hAc
  exact (isClosed_twoNullIdeal G).mem_of_tendsto hlim (Eventually.of_forall hj)

end

end UniformTracialTwoNullIdeal
end GroupApproximation
