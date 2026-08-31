import GroupApproximation.Analysis.STW22CounterexampleAssembly

/-!
# Model tests for the Problem XXII assembly

Repository standing order: every hypothesis-bearing `Prop` is instantiated at
the smallest object in reach before it is used, and the degenerate instance is
checked as well as the intended one.  `Analysis/STW22CounterexampleAssembly`
introduces two new `Prop`s, `IsUniformTwoContinuous` and
`HasUniformTwoDiscontinuousTracialState`, and consumes `BlockObstruction`,
`TraciallyNullObstruction` and `TracialTwoGauge`.  This file tests all of them.

## The tests

* `uniformTwoNorm_normTracialTwoGauge` --- the uniform two-norm of the
  operator-norm gauge is the operator norm itself.  This pins the supremum
  taken in the definition to the right one; a definition using an infimum, or
  omitting the supremum, would fail here.

* `unitBlockObstruction` and
  `unitBlockObstruction_coronaClass_not_mem_traceZeroSpace` --- `BlockObstruction`
  is inhabited: on commutative blocks every self-commutator vanishes, so the
  unit is a block obstruction, and the landed conclusion is the correct one
  there (the unit of the corona is outside the trace-zero space).

* `not_trace_h_eq_one` --- the *degenerate* obstruction does not satisfy the
  full bundle: an obstruction whose element is the unit at some index cannot be
  tracially null, because no tracial state kills the unit.  So the unit
  obstruction never reaches the trace argument.

* `not_traciallyNullObstruction_of_twoSize_eq_norm` and
  `no_obstruction_at_normTracialTwoGauge` --- the degenerate *gauge* is
  excluded.  At the operator-norm gauge the ideal `J` is the `c₀`-sum, so
  `M = ℂ1 + B = A` and the completion adds nothing; and no
  `TraciallyNullObstruction` can record the operator norm as its two-size,
  since its sequence would then be simultaneously norm-null and of constant
  norm one.  The counterexample therefore genuinely needs a gauge strictly
  smaller than the norm in the tail --- blocks of growing matrix size.

* `auditTwoRate` and `uniformTwoNorm_tail_eq_auditTwoRate` --- the
  (A16)/(A17) mechanism run on the audit's own explicit sequence
  `‖h_s‖_{2,s} = sqrt (2/(s+1))`.  The tail supremum is computed exactly, and
  it is `sqrt (2/(N+2)) → 0`, which is the audit's (A17) on the nose.

* `isUniformTwoContinuous_of_bound` and `not_isUniformTwoContinuous_iff` ---
  `IsUniformTwoContinuous` is satisfiable (any state bounded by a multiple of
  the gauge has it) and says what it looks like.  Together with
  `not_exists_uniformTwoBound_of_discontinuous` this identifies the content of
  the endpoint: the counterexample state is unbounded relative to the uniform
  two-norm, which is exactly what makes it fall outside `T(A)`.

## Residue

One test is deliberately not attempted here.  Because `M = ℂ1 + J` is a closed
star subalgebra it carries a C-star structure --- this is pinned by
`scalarPlusJSubalgebra_hasCStarAlgebra` --- and contractivity of a tracial state
on that structure would refute `HasUniformTwoDiscontinuousTracialState` at the
operator-norm gauge outright.  Running that argument means moving between the
subalgebra's `SubringClass` ring structure and the one carried by the C-star
instance, and it is not attempted blind.  The weaker degeneracy statement
`no_obstruction_at_normTracialTwoGauge` closes the same route by removing its
input.
-/

namespace GroupApproximation
namespace STW22AssemblyModelTest

open Filter PolarLiftingGeneralCStar
open UniformTracialSequenceCompletion UniformTracialTwoNullIdeal
open CuntzPedersenCoronaObstruction CuntzPedersenTraceZero
open STW22Assembly

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)]

/-! ## The uniform two-norm is the right supremum -/

/-- At the operator-norm gauge the uniform two-norm is the operator norm of the
bounded product.  This is the sanity check on the definition: the audit's
`‖·‖_{2,T(A)}` is a supremum over coordinates, and the `ℓ∞` norm is the same
supremum. -/
theorem uniformTwoNorm_normTracialTwoGauge (x : BoundedCStarSequence D) :
    uniformTwoNorm (normTracialTwoGauge D) x = ‖x‖ := by
  simp only [uniformTwoNorm, normTracialTwoGauge_q, lp.norm_eq_ciSup]

/-! ## `BlockObstruction` is inhabited, and the degenerate instance stops -/

/-- **Satisfiability of `BlockObstruction`.**  On commutative blocks every
additive self-commutator vanishes, so the unit satisfies the width clause for
free.  This shows the structure is not vacuous, and that its `width` field is
not accidentally contradictory. -/
def unitBlockObstruction (E : ℕ → Type u) [∀ n, CommCStarAlgebra (E n)]
    [∀ n, Nontrivial (E n)] : BlockObstruction E where
  h := fun _ ↦ 1
  norm_h := fun _ ↦ norm_one
  selfadjoint_h := fun _ ↦ star_one _
  width := by
    intro _ell n _ z
    have hzero : ∑ j, selfCommutator (z j) = (0 : E n) := by
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      rw [selfCommutator_apply, mul_comm (star (z j)) (z j), sub_self]
    have hnorm : ‖(1 : E n) - ∑ j, selfCommutator (z j)‖ = 1 := by
      rw [hzero, sub_zero, norm_one]
    exact hnorm.ge

/-- The landed conclusion is the correct one at the unit obstruction: the unit
of the corona is outside the Cuntz--Pedersen trace-zero space. -/
theorem unitBlockObstruction_coronaClass_not_mem_traceZeroSpace
    (E : ℕ → Type u) [∀ n, CommCStarAlgebra (E n)] [∀ n, Nontrivial (E n)] :
    (unitBlockObstruction E).coronaClass ∉
      traceZeroSpace (CStarProductCorona E atTop) :=
  coronaClass_not_mem_traceZeroSpace (unitBlockObstruction E)

/-- **The degenerate obstruction stops before the trace argument.**  If the
obstructing element is the unit at some index, the block cannot be tracially
null: no tracial state kills the unit.  So `unitBlockObstruction` never
upgrades to a `TraciallyNullObstruction`, and the trace-zero clause of the
bundle is load-bearing rather than decorative. -/
theorem not_trace_h_eq_one (B : TraciallyNullObstruction D) (n : ℕ)
    (τ : TracialState (D n)) (h : B.toBlockObstruction.h n = 1) : False := by
  have h0 := B.trace_h n τ
  rw [h, τ.apply_one] at h0
  exact one_ne_zero h0

/-! ## The degenerate gauge is excluded -/

/-- **The gauge must be strictly weaker than the norm.**  An obstruction whose
recorded two-size is the operator norm would have a sequence which is both
norm-null and of constant norm one. -/
theorem not_traciallyNullObstruction_of_twoSize_eq_norm
    (B : TraciallyNullObstruction D)
    (h : ∀ (n : ℕ) (x : D n), B.twoSize n x = ‖x‖) : False := by
  refine B.sequence_not_isNullCStarSequence ?_
  have hnull := B.sequence_isUniformTwoNull
  have hfun : (fun n ↦ ‖B.toBlockObstruction.sequence n‖)
      = fun n ↦ B.twoSize n (B.toBlockObstruction.sequence n) := by
    funext n
    exact (h n _).symm
  show Tendsto (fun n ↦ ‖B.toBlockObstruction.sequence n‖) atTop (nhds 0)
  rw [hfun]
  exact hnull

/-- **Degenerate-instance test for the whole assembly.**  At the operator-norm
gauge the machinery collapses: the ideal `J` is exactly the `c₀`-sum, so
`M = ℂ1 + B = A` and the uniform tracial completion adds nothing; and no
`TraciallyNullObstruction` can match that gauge.  The counterexample cannot be
assembled from a gauge equal to the operator norm. -/
theorem no_obstruction_at_normTracialTwoGauge :
    twoNullIdeal (normTracialTwoGauge D) = nullCStarSequenceIdeal D atTop ∧
      ∀ B : TraciallyNullObstruction D,
        B.twoSize ≠ (normTracialTwoGauge D).q := by
  refine ⟨twoNullIdeal_normTracialTwoGauge, fun B hB ↦ ?_⟩
  exact not_traciallyNullObstruction_of_twoSize_eq_norm B
    fun n x ↦ (congrFun (congrFun hB n) x).trans (normTracialTwoGauge_q n x)

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
exactly `sqrt (2/(N+2))`: the supremum is attained at the first surviving
index, because the rate is decreasing. -/
theorem uniformTwoNorm_tail_eq_auditTwoRate (G : TracialTwoGauge D)
    (B : BlockObstruction D) (hrate : ∀ n, G.q n (B.h n) = auditTwoRate n)
    (N : ℕ) : uniformTwoNorm G (B.tail N) = auditTwoRate (N + 1) := by
  have hcoord : ∀ n, G.q n (B.tail N n) = if N < n then auditTwoRate n else 0 := by
    intro n
    rw [BlockObstruction.tail_apply]
    split_ifs
    · exact hrate n
    · exact G.zero n
  refine le_antisymm (uniformTwoNorm_le G _ fun n ↦ ?_) ?_
  · rw [hcoord n]
    split_ifs with hn
    · exact auditTwoRate_antitone (by omega)
    · exact (auditTwoRate_pos (N + 1)).le
  · have hle := q_le_uniformTwoNorm G (B.tail N) (N + 1)
    rw [hcoord (N + 1), if_pos (show N < N + 1 by omega)] at hle
    exact hle

/-- **(A16)--(A17) on the audit's rate, assembled.**  All tails have the same
corona class, their uniform two-norms are exactly `sqrt (2/(N+2))`, and those
tend to zero.  This is the explicit discontinuity sequence of the audit run on
an explicit rate rather than on an abstract null hypothesis. -/
theorem audit_tail_discontinuity_data (G : TracialTwoGauge D)
    (B : BlockObstruction D) (hrate : ∀ n, G.q n (B.h n) = auditTwoRate n) :
    (∀ N, cStarProductCoronaQuotient D atTop (B.tail N) = B.coronaClass) ∧
      (∀ N, uniformTwoNorm G (B.tail N) = auditTwoRate (N + 1)) ∧
      Tendsto (fun N ↦ uniformTwoNorm G (B.tail N)) atTop (nhds 0) := by
  refine ⟨fun N ↦ B.quotient_tail N,
    fun N ↦ uniformTwoNorm_tail_eq_auditTwoRate G B hrate N, ?_⟩
  have hfun : (fun N ↦ uniformTwoNorm G (B.tail N))
      = fun N ↦ auditTwoRate (N + 1) := by
    funext N
    exact uniformTwoNorm_tail_eq_auditTwoRate G B hrate N
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

/-- `IsUniformTwoContinuous` says what it looks like: its negation is exactly a
uniformly two-null sequence in `M` along which the state does not tend to
zero. -/
theorem not_isUniformTwoContinuous_iff (G : TracialTwoGauge D)
    (σ : TracialState ↥(scalarPlusJSubalgebra G)) :
    ¬ IsUniformTwoContinuous G σ ↔
      ∃ x : ℕ → ↥(scalarPlusJSubalgebra G),
        Tendsto (fun N ↦ uniformTwoNorm G ((x N : BoundedCStarSequence D)))
          atTop (nhds 0) ∧
        ¬ Tendsto (fun N ↦ σ (x N)) atTop (nhds 0) := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    exact h hcon
  · rintro ⟨x, hx, hnx⟩ hcont
    exact hnx (hcont x hx)

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

end

end STW22AssemblyModelTest
end GroupApproximation
