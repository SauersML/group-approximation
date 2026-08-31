import GroupApproximation.Analysis.STW22CounterexampleAssembly
import GroupApproximation.Analysis.AntipodalHomogeneousBlock

/-!
# Model tests for the Problem XXII assembly

Repository standing order: every hypothesis-bearing `Prop` is instantiated at
the smallest object in reach before it is used, and the degenerate instance is
checked as well as the intended one.  The assembly introduces
`CoordinateStateBlockData`, `IsUniformTwoContinuous` and
`HasUniformTwoDiscontinuousTracialState`, and consumes
`ArbitrarilyLateCoordinateStateConstraints` and `TracialTwoGauge`.  This file
tests all of them.

## The tests

* `uniformTwoNorm_normTracialTwoGauge` --- the uniform two-norm of the
  operator-norm gauge is the operator norm itself.  This pins the supremum in
  the definition to the right one.

* `arbitrarilyLateCoordinateStateConstraints_one` --- the compactness
  hypothesis is **satisfiable**: on commutative blocks every self-commutator
  vanishes, so any state at any coordinate solves the constraints for the
  constant unit sequence.  Running the landed compactness theorem on it
  produces a corona trace taking the value one on the unit, which is the right
  answer there.

* `not_arbitrarilyLateCoordinateStateConstraints_zero` --- and it is **not
  vacuous**: the zero sequence fails it, because a state cannot send zero to
  one.  So the hypothesis really does pick out sequences with a nonzero corona
  class.

* `no_blockData_at_normTracialTwoGauge` --- the *degenerate gauge* is excluded
  in one line.  At the operator-norm gauge, `gauge_tendsto_zero` says the
  sequence is norm-null, which the coordinate states forbid.  So no
  `CoordinateStateBlockData` exists there, `J` is the `c₀`-sum, `M = A`, and the
  counterexample genuinely needs a gauge strictly smaller than the operator norm
  in the tail --- blocks of growing matrix size.

* `auditTwoRate` and `uniformTwoNorm_tail_eq_auditTwoRate` --- the
  (A16)/(A17) mechanism run on the audit's own explicit sequence
  `‖h_s‖_{2,s} = sqrt (2/(s+1))`.  The tail supremum is computed exactly and is
  `sqrt (2/(N+2)) → 0`, which is (A17) on the nose.

* `isUniformTwoContinuous_of_bound` and
  `not_exists_uniformTwoBound_of_discontinuous` --- `IsUniformTwoContinuous` is
  satisfiable (any state bounded by a multiple of the gauge has it), and the
  content of the endpoint is that the counterexample state is unbounded relative
  to the uniform two-norm, which is what separates it from `T(A)`.

* `realProjectiveBlock_hasCStarAlgebra` --- interface check on the block model:
  the antipodally covariant matrix functions of
  `Analysis/AntipodalHomogeneousBlock` carry the C-star structure the assembly
  requires, so `D s := RealProjectiveBlock d s` is a legal instantiation.

## Residue

The assembly also asks for `Nontrivial (D n)` at every coordinate.  For the
antipodal blocks this holds because the fixed-point algebra contains the
scalars and `S^d` is nonempty, but neither `Nonempty (Sphere d)` nor the
resulting `Nontrivial (RealProjectiveBlock d s)` is landed, so the instantiation
check here stops at the C-star structure.
-/

namespace GroupApproximation
namespace STW22AssemblyModelTest

open Filter PolarLiftingGeneralCStar
open UniformTracialSequenceCompletion UniformTracialTwoNullIdeal
open CuntzPedersenCoronaObstruction
open CStarState CoronaCoordinateStateCompactness
open STW22Assembly

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)]

/-! ## The uniform two-norm is the right supremum -/

/-- At the operator-norm gauge the uniform two-norm is the operator norm of the
bounded product.  The audit's `‖·‖_{2,T(A)}` is a supremum over coordinates, and
the `ℓ∞` norm is the same supremum. -/
theorem uniformTwoNorm_normTracialTwoGauge (x : BoundedCStarSequence D) :
    uniformTwoNorm (normTracialTwoGauge D) x = ‖x‖ := by
  simp only [uniformTwoNorm, normTracialTwoGauge_q, lp.norm_eq_ciSup]

/-! ## The compactness hypothesis is satisfiable and not vacuous -/

/-- **Satisfiability.**  On commutative blocks every additive self-commutator
vanishes, so the constraints are solved at every coordinate by any state, and
the constant unit sequence carries them.  This shows the `Prop` consumed by the
compactness theorem is inhabited, and that its two clauses are not jointly
contradictory. -/
theorem arbitrarilyLateCoordinateStateConstraints_one
    (E : ℕ → Type u) [∀ n, CommCStarAlgebra (E n)] [∀ n, Nontrivial (E n)] :
    ArbitrarilyLateCoordinateStateConstraints (1 : BoundedCStarSequence E) := by
  intro S floor
  obtain ⟨ψ, -⟩ := State.exists_star_mul_self (1 : E floor)
  refine ⟨floor, le_rfl, ψ, ?_, ?_⟩
  · have hone : ((1 : BoundedCStarSequence E) floor) = (1 : E floor) := rfl
    rw [hone]
    exact ψ.map_one
  · intro z _
    have hz : selfCommutator (z floor) = (0 : E floor) := by
      rw [selfCommutator_apply, mul_comm (star (z floor)) (z floor), sub_self]
    rw [hz, map_zero]

/-- The landed compactness theorem run on that instance gives the right answer:
a tracial state of the corona sending the class of the unit to one. -/
theorem exists_corona_tracialState_one
    (E : ℕ → Type u) [∀ n, CommCStarAlgebra (E n)] [∀ n, Nontrivial (E n)] :
    ∃ σ : TracialState (CStarProductCorona E atTop),
      σ (cStarProductCoronaQuotient E atTop 1) = 1 :=
  exists_corona_tracialState_of_arbitrarilyLate_coordinate_states
    (1 : BoundedCStarSequence E) (arbitrarilyLateCoordinateStateConstraints_one E)

/-- **Not vacuous.**  The zero sequence fails the constraints, since a state
cannot send it to one.  Together with the previous test this pins the
hypothesis between a genuine positive instance and a genuine negative one. -/
theorem not_arbitrarilyLateCoordinateStateConstraints_zero :
    ¬ ArbitrarilyLateCoordinateStateConstraints (0 : BoundedCStarSequence D) := by
  intro hcoord
  refine not_isNull_of_arbitrarilyLateCoordinateStates hcoord ?_
  exact zero_mem _

/-! ## The degenerate gauge is excluded -/

/-- **Degenerate-instance test for the whole assembly.**  At the operator-norm
gauge the bundle is contradictory: `gauge_tendsto_zero` then says the
obstruction is norm-null, which is exactly what the coordinate states forbid.
So `J` is the `c₀`-sum, `M = ℂ1 + B = A`, and the counterexample cannot be
assembled from a gauge equal to the operator norm. -/
theorem no_blockData_at_normTracialTwoGauge
    (B : CoordinateStateBlockData D (normTracialTwoGauge D)) : False :=
  B.not_isNull B.gauge_tendsto_zero

/-! ## (A16)--(A17) on the audit's explicit rate

The audit's blocks have `‖h_s‖_{2,s} = sqrt (2/(s+1))` by (A1), with `s ≥ 1`.
Indexing from `s = n + 1` gives the rate below. -/

/-- The audit's (A1) rate, with the audit's block index `s` written `n + 1`. -/
def auditTwoRate (n : ℕ) : ℝ := Real.sqrt (2 / ((n : ℝ) + 2))

theorem auditTwoRate_pos (n : ℕ) : 0 < auditTwoRate n := by
  have h : (0 : ℝ) < 2 / ((n : ℝ) + 2) := by positivity
  exact Real.sqrt_pos.mpr h

theorem auditTwoRate_antitone : Antitone auditTwoRate := by
  intro m n hmn
  have hcast : (m : ℝ) + 2 ≤ (n : ℝ) + 2 := by
    have hle : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hmn
    linarith
  have hdiv : (2 : ℝ) / ((n : ℝ) + 2) ≤ 2 / ((m : ℝ) + 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hcast
  exact Real.sqrt_le_sqrt hdiv

theorem auditTwoRate_tendsto_zero : Tendsto auditTwoRate atTop (nhds 0) := by
  have htop : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun n : ℕ ↦ (2 : ℝ) / ((n : ℝ) + 2)) atTop (nhds 0) :=
    htop.const_div_atTop 2
  have hs : Tendsto (fun n : ℕ ↦ Real.sqrt ((2 : ℝ) / ((n : ℝ) + 2))) atTop
      (nhds (Real.sqrt 0)) := hd.sqrt
  rw [Real.sqrt_zero] at hs
  exact hs

/-- **(A17) computed exactly.**  If the coordinate gauges of the obstruction are
the audit's `sqrt (2/(s+1))`, then the uniform two-norm of the `N`-th tail is
exactly `sqrt (2/(N+2))`: the supremum is attained at the first surviving index,
because the rate is decreasing. -/
theorem uniformTwoNorm_tail_eq_auditTwoRate (G : TracialTwoGauge D)
    (x : BoundedCStarSequence D) (hrate : ∀ n, G.q n (x n) = auditTwoRate n)
    (N : ℕ) : uniformTwoNorm G (tail x N) = auditTwoRate (N + 1) := by
  have hcoord : ∀ n, G.q n (tail x N n)
      = if n ≤ N then 0 else auditTwoRate n := by
    intro n
    rw [tail_apply]
    split_ifs
    · exact G.zero n
    · exact hrate n
  refine le_antisymm (uniformTwoNorm_le G _ fun n ↦ ?_) ?_
  · rw [hcoord n]
    split_ifs with hn
    · exact (auditTwoRate_pos (N + 1)).le
    · exact auditTwoRate_antitone (by omega)
  · have hle := q_le_uniformTwoNorm G (tail x N) (N + 1)
    rw [hcoord (N + 1), if_neg (show ¬ N + 1 ≤ N by omega)] at hle
    exact hle

/-- **(A16)--(A17) on the audit's rate, assembled.**  All tails have the same
corona class, their uniform two-norms are exactly `sqrt (2/(N+2))`, and those
tend to zero.  This is the audit's explicit discontinuity sequence run on an
explicit rate rather than on an abstract null hypothesis. -/
theorem audit_tail_discontinuity_data (G : TracialTwoGauge D)
    (x : BoundedCStarSequence D) (hrate : ∀ n, G.q n (x n) = auditTwoRate n) :
    (∀ N, cStarProductCoronaQuotient D atTop (tail x N)
        = cStarProductCoronaQuotient D atTop x) ∧
      (∀ N, uniformTwoNorm G (tail x N) = auditTwoRate (N + 1)) ∧
      Tendsto (fun N ↦ uniformTwoNorm G (tail x N)) atTop (nhds 0) := by
  refine ⟨fun N ↦ corona_tail_eq x N,
    fun N ↦ uniformTwoNorm_tail_eq_auditTwoRate G x hrate N, ?_⟩
  have hfun : (fun N ↦ uniformTwoNorm G (tail x N))
      = fun N ↦ auditTwoRate (N + 1) := by
    funext N
    exact uniformTwoNorm_tail_eq_auditTwoRate G x hrate N
  rw [hfun]
  exact auditTwoRate_tendsto_zero.comp (tendsto_add_atTop_nat 1)

/-! ## The two new `Prop`s -/

/-- **Satisfiability of `IsUniformTwoContinuous`.**  A state bounded by a
multiple of the uniform two-norm is continuous for it.  A tracial state of `A`
extends to `M` with the bound `K = 1`, so the property is inhabited and the
endpoint is not a statement about an empty class. -/
theorem isUniformTwoContinuous_of_bound (G : TracialTwoGauge D)
    (σ : TracialState ↥(scalarPlusJSubalgebra G)) {K : ℝ}
    (hK : ∀ x : ↥(scalarPlusJSubalgebra G),
      ‖σ x‖ ≤ K * uniformTwoNorm G (x : BoundedCStarSequence D)) :
    IsUniformTwoContinuous G σ := by
  intro x hx
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    (Eventually.of_forall fun N ↦ hK (x N)) ?_
  have h := hx.const_mul K
  rwa [mul_zero] at h

/-- **The content of the endpoint.**  A tracial state witnessing
`HasUniformTwoDiscontinuousTracialState` is unbounded relative to the uniform
two-norm: for every constant `K` some element of `M` violates the bound.  This
is the contrapositive of `isUniformTwoContinuous_of_bound`, and it is what
separates the state from the extensions of `T(A)`. -/
theorem not_exists_uniformTwoBound_of_discontinuous (G : TracialTwoGauge D)
    (σ : TracialState ↥(scalarPlusJSubalgebra G))
    (hσ : ¬ IsUniformTwoContinuous G σ) (K : ℝ) :
    ∃ x : ↥(scalarPlusJSubalgebra G),
      K * uniformTwoNorm G (x : BoundedCStarSequence D) < ‖σ x‖ := by
  by_contra hcon
  push_neg at hcon
  exact hσ (isUniformTwoContinuous_of_bound G σ hcon)

/-! ## The block model fits the interface -/

/-- Interface check on the concrete blocks: the antipodally covariant matrix
functions over `RP^d` are a C-star algebra, so `D s := RealProjectiveBlock d s`
is a legal instantiation of every theorem in the assembly.  The remaining
instance the assembly asks for, `Nontrivial`, is recorded as residue in this
file's header. -/
theorem realProjectiveBlock_hasCStarAlgebra (d s : ℕ) :
    Nonempty (CStarAlgebra (STW22.RealProjectiveBlock d s)) :=
  ⟨inferInstance⟩

end

end STW22AssemblyModelTest
end GroupApproximation
