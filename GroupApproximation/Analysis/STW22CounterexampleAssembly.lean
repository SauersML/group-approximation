import GroupApproximation.Analysis.UniformTracialCompletionIdentification
import GroupApproximation.Analysis.CuntzPedersenJordanTracial

/-!
# Sections 5--7 of the STW Problem XXII counterexample audit, assembled

`research/artifacts/stw22-trace-problem-counterexample-audit-2026-08-31.md`
ends with three steps, and this file is their composition:

* **(A10)--(A13)**  the obstructing class `hbar = h + B` in the corona keeps
  distance at least one from every finite sum of self-commutators, so it is
  outside the Cuntz--Pedersen trace-zero space;
* **(A14)--(A15)**  Cuntz--Pedersen separation, refined by the Jordan
  decomposition, produces `sigma` in `T(H)` with `sigma hbar ≠ 0`, and its
  pullback `sigma_tilde` along the quotient is a tracial state of
  `M = ℂ1 + J`;
* **(A16)--(A18)**  `sigma_tilde` is constant and nonzero on the tail
  truncations `h^(n)`, whose uniform two-norms tend to zero.  So
  `sigma_tilde` is a tracial state of `M` which is not continuous for the
  gauge, i.e. `T(A) ⊊ T(M)`.

## What is composed, and what is assumed

Every step below is a composition of already-landed material:

* `Analysis/CuntzPedersenCoronaObstruction` supplies `BlockObstruction`,
  `TraciallyNullObstruction`, the limsup bound
  `norm_coronaClass_sub_sum_selfCommutator_ge_one`, and (A13) itself as
  `coronaClass_not_mem_traceZeroSpace`;
* `Analysis/CuntzPedersenJordanTracial` supplies
  `exists_tracialState_detecting_coronaClass_of_jordan`, whose only unproved
  inputs are the two named Jordan properties;
* `Analysis/UniformTracialTwoNullIdeal` and
  `Analysis/UniformTracialCompletionIdentification` supply `J`, the star
  subalgebra `M = ℂ1 + J`, its norm closedness, and (A8).

Nothing here is an axiom.  The unproved inputs are exactly three named
`Prop`s, all of them visible in the dependency surface of the summary theorem:

* `HasJordanDecomposition` and `HasUniqueJordanDecomposition` on the corona
  (Cuntz--Pedersen; Takesaki III.4.2);
* the `width` field of `BlockObstruction`, which is the audit's (A2), the
  Chern-class compression bound.  `Analysis/ChernCommonZeroBridge` derives that
  bound from `CommonZeroProperty`, and derives it unconditionally at the
  `s = ℓ = 1` block.

The two remaining structural facts of the audit -- that `A` is type I and that
`T(A)` is Bauer -- are Sections 1 and 3, assembled separately in
`Analysis/STW22CounterexampleStructure`.  They are not needed for the trace
statement and are not repeated here.

## The corona used

The audit forms `H = M/B`.  This file uses instead the corona
`(∏_s D_s)/B` of the whole bounded product, together with the composite
`M ↪ ∏_s D_s → (∏_s D_s)/B`.  The two give the same conclusion, and the
larger corona is the strictly stronger route:

* for (A12), arbitrary bounded lifts are allowed, which is more competitors
  than lifts from `M`, so the distance bound obtained is at least as strong;
* for (A14), the resulting tracial state restricts to a tracial state of `M`
  along the composite, which is exactly `sigma_tilde`.

`exists_mem_twoNullIdeal_selfCommutator_eq` records the audit's remark that
lifting from `M` costs nothing, because scalar parts cancel in
self-commutators.

`STW22CounterexampleAssemblyModelTest` model-tests every `Prop` introduced
here.
-/

namespace GroupApproximation
namespace STW22Assembly

open Filter PolarLiftingGeneralCStar
open UniformTracialSequenceCompletion UniformTracialTwoNullIdeal
open UniformTracialCompletionIdentification
open CuntzPedersenCoronaObstruction CuntzPedersenTraceZero
open CuntzPedersenJordanTracial

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)]

/-! ## The uniform two-norm

Hostile check 2 of the audit: for a positive element the supremum of the
tracial two-norms over `T(A) = Prob(K)` is attained on point masses, so the
uniform two-norm is the supremum of the coordinate gauges.  That supremum is
taken as the definition here, which keeps the statement independent of the
still-unformalized identification `T(A) = Prob(K)`. -/

/-- The audit's `‖·‖_{2,T(A)}`: the supremum over coordinates of the coordinate
two-gauges. -/
def uniformTwoNorm (G : TracialTwoGauge D) (x : BoundedCStarSequence D) : ℝ :=
  ⨆ n, G.q n (x n)

theorem bddAbove_range_q (G : TracialTwoGauge D) (x : BoundedCStarSequence D) :
    BddAbove (Set.range fun n ↦ G.q n (x n)) := by
  refine ⟨‖x‖, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (G.le_norm n (x n)).trans (boundedCStarSequence_coord_norm_le D x n)

theorem q_le_uniformTwoNorm (G : TracialTwoGauge D)
    (x : BoundedCStarSequence D) (n : ℕ) :
    G.q n (x n) ≤ uniformTwoNorm G x :=
  le_ciSup (bddAbove_range_q G x) n

theorem uniformTwoNorm_nonneg (G : TracialTwoGauge D)
    (x : BoundedCStarSequence D) : 0 ≤ uniformTwoNorm G x :=
  (G.nonneg 0 (x 0)).trans (q_le_uniformTwoNorm G x 0)

theorem uniformTwoNorm_le (G : TracialTwoGauge D) (x : BoundedCStarSequence D)
    {c : ℝ} (h : ∀ n, G.q n (x n) ≤ c) : uniformTwoNorm G x ≤ c :=
  ciSup_le h

/-- The uniform two-norm is dominated by the operator norm, as every gauge is
coordinatewise. -/
theorem uniformTwoNorm_le_norm (G : TracialTwoGauge D)
    (x : BoundedCStarSequence D) : uniformTwoNorm G x ≤ ‖x‖ :=
  uniformTwoNorm_le G x fun n ↦
    (G.le_norm n (x n)).trans (boundedCStarSequence_coord_norm_le D x n)

/-! ## (A12): scalar parts cancel in self-commutators -/

/-- Adding a scalar multiple of the unit leaves a self-commutator unchanged.
This is the audit's "scalar parts cancel in self-commutators" of (A12): a lift
`λ1 + z` of an element of `H = M/B` contributes the same self-commutator as its
ideal part `z`. -/
theorem selfCommutator_smul_one_add {C : Type*} [CStarAlgebra C] (c : ℂ)
    (y : C) : selfCommutator (c • (1 : C) + y) = selfCommutator y := by
  have hs : star (c • (1 : C) + y) = star c • (1 : C) + star y := by
    rw [star_add, star_smul, star_one]
  have hsw : star (star c • (1 : C) + star y) = c • (1 : C) + y := by
    rw [star_add, star_smul, star_one, star_star, star_star]
  have h1 := CuntzPedersenJordanTracial.star_smul_one_add_mul_self c y
  have h2 := CuntzPedersenJordanTracial.star_smul_one_add_mul_self (star c) (star y)
  rw [star_star, star_star, hsw] at h2
  have hcomm : star c * c = c * star c := mul_comm _ _
  rw [selfCommutator_apply, selfCommutator_apply, h1, hs, h2, hcomm]
  abel

/-- The same statement written with the algebra map, which is the form in which
`ℂ1 + J` is defined. -/
theorem selfCommutator_algebraMap_add {C : Type*} [CStarAlgebra C] (c : ℂ)
    (z : C) : selfCommutator (algebraMap ℂ C c + z) = selfCommutator z := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact selfCommutator_smul_one_add c z

/-- Every element of `M = ℂ1 + J` has the same self-commutator as one element of
the ideal `J`. -/
theorem exists_mem_twoNullIdeal_selfCommutator_eq (G : TracialTwoGauge D)
    {y : BoundedCStarSequence D} (hy : y ∈ scalarPlusJ G) :
    ∃ z ∈ twoNullIdeal G, selfCommutator y = selfCommutator z := by
  obtain ⟨c, j, hj, rfl⟩ := hy
  exact ⟨j, hj, selfCommutator_algebraMap_add c j⟩

/-- **(A12) with lifts from `M`.**  Take any finitely many elements of `M`.
Their scalar parts cancel in the self-commutators, so the sum of those
self-commutators is the sum for a family drawn from the ideal `J`, and the
landed limsup bound applies: the obstructing corona class stays at distance at
least one from that sum. -/
theorem norm_coronaClass_sub_sum_selfCommutator_scalarPlusJ_ge_one
    (G : TracialTwoGauge D) (B : BlockObstruction D) (ell : ℕ)
    (y : Fin ell → BoundedCStarSequence D) (hy : ∀ j, y j ∈ scalarPlusJ G) :
    ∃ z : Fin ell → BoundedCStarSequence D,
      (∀ j, z j ∈ twoNullIdeal G) ∧
      (∀ j, selfCommutator (y j) = selfCommutator (z j)) ∧
      1 ≤ ‖B.coronaClass -
        ∑ j, selfCommutator (cStarProductCoronaQuotient D atTop (z j))‖ := by
  choose z hz hzeq using fun j ↦ exists_mem_twoNullIdeal_selfCommutator_eq G (hy j)
  exact ⟨z, hz, hzeq, norm_coronaClass_sub_sum_selfCommutator_ge_one B ell z⟩

/-! ## `M = ℂ1 + J`, its C-star structure, and the quotient map -/

/-- The ideal `J` sits inside `M = ℂ1 + J`. -/
theorem twoNullIdeal_le_scalarPlusJ (G : TracialTwoGauge D)
    {x : BoundedCStarSequence D} (hx : x ∈ twoNullIdeal G) :
    x ∈ scalarPlusJ G :=
  ⟨0, x, hx, by rw [map_zero, zero_add]⟩

/-- Audit pin: `M = ℂ1 + J` is a genuine C-star algebra, being a norm-closed
star subalgebra of the bounded product.  Nothing below uses this instance; it
records that the tracial states produced here really are tracial states of a
C-star algebra, as the audit asserts. -/
theorem scalarPlusJSubalgebra_hasCStarAlgebra (G : TracialTwoGauge D) :
    Nonempty (CStarAlgebra ↥(scalarPlusJSubalgebra G)) := by
  haveI : IsClosed ((scalarPlusJSubalgebra G : Set (BoundedCStarSequence D))) := by
    rw [coe_scalarPlusJSubalgebra]
    exact isClosed_scalarPlusJ G
  exact ⟨inferInstance⟩

/-- The audit's `π : M → H` of (A10), realized as the restriction to `M` of the
quotient of the whole bounded product by the `c₀`-sum `B`. -/
def completionToCorona (G : TracialTwoGauge D) :
    ↥(scalarPlusJSubalgebra G) →⋆ₐ[ℂ] CStarProductCorona D atTop :=
  (cStarProductCoronaQuotient D atTop).comp (scalarPlusJSubalgebra G).subtype

@[simp] theorem completionToCorona_apply (G : TracialTwoGauge D)
    (x : ↥(scalarPlusJSubalgebra G)) :
    completionToCorona G x =
      cStarProductCoronaQuotient D atTop (x : BoundedCStarSequence D) := rfl

/-- **(A15).**  `sigma_tilde = sigma ∘ π`, the pullback of a corona trace to
`M = ℂ1 + J`. -/
def pullbackTracialState (G : TracialTwoGauge D)
    (σ : TracialState (CStarProductCorona D atTop)) :
    TracialState ↥(scalarPlusJSubalgebra G) :=
  σ.compStarAlgHom (completionToCorona G)

@[simp] theorem pullbackTracialState_apply (G : TracialTwoGauge D)
    (σ : TracialState (CStarProductCorona D atTop))
    (x : ↥(scalarPlusJSubalgebra G)) :
    pullbackTracialState G σ x =
      σ (cStarProductCoronaQuotient D atTop (x : BoundedCStarSequence D)) := rfl

/-- **(A15) on `A`.**  The pullback kills the `c₀`-sum `B`, so on
`A = ℂ1 + B` it is the extreme trace `tau_infinity` coming from the scalar
quotient: an element of `M` whose distance to the scalar `c` is norm-null is
sent to `c`. -/
theorem pullbackTracialState_eq_of_sub_isNull (G : TracialTwoGauge D)
    (σ : TracialState (CStarProductCorona D atTop)) (c : ℂ)
    (x : ↥(scalarPlusJSubalgebra G))
    (hx : (x : BoundedCStarSequence D) -
      algebraMap ℂ (BoundedCStarSequence D) c ∈ nullCStarSequenceIdeal D atTop) :
    pullbackTracialState G σ x = c := by
  rw [pullbackTracialState_apply]
  have hq : cStarProductCoronaQuotient D atTop (x : BoundedCStarSequence D)
      = algebraMap ℂ (CStarProductCorona D atTop) c := by
    rw [← sub_eq_zero,
      ← AlgHomClass.commutes (cStarProductCoronaQuotient D atTop) c, ← map_sub]
    exact (cStarProductCoronaQuotient_eq_zero_iff D atTop _).2 hx
  rw [hq]
  exact tracialState_map_algebraMap σ c

/-- The same statement in the coordinate form in which `A = unitization(⊕_s D_s)`
is realized: if the coordinates of `x` converge in operator norm to the scalar
`c`, the pullback takes the value `c` at `x`. -/
theorem pullbackTracialState_of_tendsto_algebraMap (G : TracialTwoGauge D)
    (σ : TracialState (CStarProductCorona D atTop)) {c : ℂ}
    (x : ↥(scalarPlusJSubalgebra G))
    (hx : Tendsto
      (fun n ↦ ‖(x : BoundedCStarSequence D) n - algebraMap ℂ (D n) c‖)
      atTop (nhds 0)) :
    pullbackTracialState G σ x = c := by
  refine pullbackTracialState_eq_of_sub_isNull G σ c x ?_
  rw [mem_nullCStarSequenceIdeal_iff]
  exact hx

/-! ## (A16)--(A17): the tails -/

/-- The tails of the obstruction lie in the ideal `J`. -/
theorem tail_mem_twoNullIdeal (G : TracialTwoGauge D)
    (B : TraciallyNullObstruction D) (hq : B.twoSize = G.q) (N : ℕ) :
    B.toBlockObstruction.tail N ∈ twoNullIdeal G := by
  have h0 : Tendsto (fun n ↦ G.q n (B.toBlockObstruction.h n)) atTop (nhds 0) := by
    have h := B.twoSize_h_tendsto_zero
    rwa [hq] at h
  rw [mem_twoNullIdeal_iff]
  refine squeeze_zero' (Eventually.of_forall fun n ↦ G.nonneg n _)
    (Eventually.of_forall fun n ↦ ?_) h0
  rw [BlockObstruction.tail_apply]
  split_ifs
  · exact le_rfl
  · rw [G.zero]
    exact G.nonneg n (B.toBlockObstruction.h n)

/-- The tails of the obstruction lie in `M = ℂ1 + J`. -/
theorem tail_mem_scalarPlusJ (G : TracialTwoGauge D)
    (B : TraciallyNullObstruction D) (hq : B.twoSize = G.q) (N : ℕ) :
    B.toBlockObstruction.tail N ∈ scalarPlusJ G :=
  twoNullIdeal_le_scalarPlusJ G (tail_mem_twoNullIdeal G B hq N)

/-- **(A17).**  The uniform two-norms of the tails tend to zero.  This is the
uniform-over-coordinates form of the audit's `sup_{s ≥ n} sqrt (2/(s+1))`, with
no rate assumed. -/
theorem uniformTwoNorm_tail_tendsto_zero (G : TracialTwoGauge D)
    (B : TraciallyNullObstruction D) (hq : B.twoSize = G.q) :
    Tendsto (fun N ↦ uniformTwoNorm G (B.toBlockObstruction.tail N))
      atTop (nhds 0) := by
  have h0 : Tendsto (fun n ↦ G.q n (B.toBlockObstruction.h n)) atTop (nhds 0) := by
    have h := B.twoSize_h_tendsto_zero
    rwa [hq] at h
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hev : ∀ᶠ n in atTop, G.q n (B.toBlockObstruction.h n) < ε / 2 :=
    ((Metric.tendsto_nhds.mp h0) (ε / 2) (half_pos hε)).mono fun n hn ↦ by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (G.nonneg n _)] using hn
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  filter_upwards [eventually_ge_atTop K] with N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (uniformTwoNorm_nonneg G _)]
  have hbd : uniformTwoNorm G (B.toBlockObstruction.tail N) ≤ ε / 2 := by
    refine uniformTwoNorm_le G _ fun n ↦ ?_
    rw [BlockObstruction.tail_apply]
    split_ifs with hn
    · exact (hK n (by omega)).le
    · rw [G.zero]
      linarith
  linarith

/-! ## The endpoint -/

/-- Sequential continuity at zero, for the uniform two-norm, of a tracial state
of `M = ℂ1 + J`.

Every tracial state of `A` extends to `M` with this property, by construction
of the uniform tracial completion.  STW Problem XXII asks whether every tracial
state of `M` has it. -/
def IsUniformTwoContinuous (G : TracialTwoGauge D)
    (σ : TracialState ↥(scalarPlusJSubalgebra G)) : Prop :=
  ∀ x : ℕ → ↥(scalarPlusJSubalgebra G),
    Tendsto (fun N ↦ uniformTwoNorm G ((x N : BoundedCStarSequence D)))
      atTop (nhds 0) →
    Tendsto (fun N ↦ σ (x N)) atTop (nhds 0)

/-- **The endpoint of the audit, (A18).**  The uniform tracial completion
`M = ℂ1 + J` carries a tracial state which is not continuous for the uniform
two-norm.  Such a state is not the uniform-two-continuous extension of any
tracial state of `A`, so `T(A) ⊊ T(M)`: a negative answer to STW Problem
XXII. -/
def HasUniformTwoDiscontinuousTracialState (G : TracialTwoGauge D) : Prop :=
  ∃ σ : TracialState ↥(scalarPlusJSubalgebra G), ¬ IsUniformTwoContinuous G σ

/-- A sequence which is two-null while the state is constant and nonzero on it
refutes continuity.  This is the shape of (A16)--(A17). -/
theorem not_isUniformTwoContinuous_of_constant_value (G : TracialTwoGauge D)
    (σ : TracialState ↥(scalarPlusJSubalgebra G))
    (x : ℕ → ↥(scalarPlusJSubalgebra G)) {c : ℂ} (hc : c ≠ 0)
    (hval : ∀ N, σ (x N) = c)
    (hnull : Tendsto (fun N ↦ uniformTwoNorm G ((x N : BoundedCStarSequence D)))
      atTop (nhds 0)) :
    ¬ IsUniformTwoContinuous G σ := by
  intro hcont
  have h0 := hcont x hnull
  have hconst : Tendsto (fun N ↦ σ (x N)) atTop (nhds c) := by
    have hfun : (fun N ↦ σ (x N)) = fun _ : ℕ ↦ c := funext hval
    rw [hfun]
    exact tendsto_const_nhds
  exact hc (tendsto_nhds_unique hconst h0)

/-- **(A14)--(A18).**  From the block obstruction and the two Jordan properties
on the corona:

1. the obstructing class is outside the Cuntz--Pedersen trace-zero space, by
   the landed (A13);
2. Cuntz--Pedersen separation refined by the Jordan decomposition produces a
   tracial state `sigma` of the corona detecting it;
3. its pullback `sigma_tilde` to `M` takes the same nonzero value on every tail
   `h^(N)`, while those tails are uniformly two-null.

So `sigma_tilde` is a tracial state of `M` which is not continuous for the
gauge. -/
theorem hasUniformTwoDiscontinuousTracialState_of_jordan
    (G : TracialTwoGauge D) (B : TraciallyNullObstruction D)
    (hq : B.twoSize = G.q)
    (hJ : HasJordanDecomposition (CStarProductCorona D atTop))
    (huniq : HasUniqueJordanDecomposition (CStarProductCorona D atTop)) :
    HasUniformTwoDiscontinuousTracialState G := by
  obtain ⟨σ, hσ⟩ :=
    exists_tracialState_detecting_coronaClass_of_jordan
      B.toBlockObstruction hJ huniq
  refine ⟨pullbackTracialState G σ, ?_⟩
  refine not_isUniformTwoContinuous_of_constant_value G (pullbackTracialState G σ)
    (fun N ↦ ⟨B.toBlockObstruction.tail N, tail_mem_scalarPlusJ G B hq N⟩)
    hσ (fun N ↦ ?_) (uniformTwoNorm_tail_tendsto_zero G B hq)
  rw [pullbackTracialState_apply]
  exact tracialState_tail_eq B.toBlockObstruction σ N

/-- **Sections 5--7 of the audit in one statement.**

The hypotheses are exactly the audit's unproved inputs, all named:

* `G` and `hr`, the coordinate two-gauge with the finite-rank comparison
  `‖a‖ ≤ r s ‖a‖_{2,s}` of Section 4;
* `B` and `hq`, the block data: norm-one, self-adjoint, fibre-trace-null
  elements whose gauges tend to zero and which defeat every fixed finite
  self-commutator width at every tail index.  The width clause is the audit's
  (A2), supplied by `Analysis/ChernCommonZeroBridge`;
* `hJ` and `huniq`, the two standard Jordan statements on the corona.

The conclusions are, in order: (A8), the identification of `M = ℂ1 + J` with
the bounded uniform two-closure of `A`, together with the realization of every
uniformly two-Cauchy sequence from `A` inside the bounded product; (A1)/(A10),
`h ∈ J \ B`; the norm of the corona class; (A13); and (A18). -/
theorem stw22_trace_problem_counterexample
    (G : TracialTwoGauge D) {r : ℕ → ℝ} (hr : IsCoordinateNormComparison G r)
    (B : TraciallyNullObstruction D) (hq : B.twoSize = G.q)
    (hJ : HasJordanDecomposition (CStarProductCorona D atTop))
    (huniq : HasUniqueJordanDecomposition (CStarProductCorona D atTop)) :
    scalarPlusJ G =
        {x : BoundedCStarSequence D |
          IsBoundedUniformTwoApproximable G.toUniformTwoGauge
            (unitizedC0Sum D) x} ∧
      (∀ a : ℕ → BoundedCStarSequence D, (∀ k, a k ∈ unitizedC0Sum D) →
        ∀ C : ℝ, (∀ k, ‖a k‖ ≤ C) →
        (∀ ε > 0, ∃ K, ∀ k, K ≤ k → ∀ l, K ≤ l → ∀ n,
          G.q n (a k n - a l n) < ε) →
        ∃ y : BoundedCStarSequence D, y ∈ scalarPlusJ G ∧
          ∀ ε > 0, ∃ K, ∀ k, K ≤ k → ∀ n, G.q n (y n - a k n) < ε) ∧
      B.toBlockObstruction.sequence ∈ twoNullIdeal G ∧
      B.toBlockObstruction.sequence ∉ nullCStarSequenceIdeal D atTop ∧
      ‖B.toBlockObstruction.coronaClass‖ = 1 ∧
      B.toBlockObstruction.coronaClass ∉
        traceZeroSpace (CStarProductCorona D atTop) ∧
      HasUniformTwoDiscontinuousTracialState G := by
  obtain ⟨hmemJ, hnotB⟩ := obstruction_mem_twoNullIdeal_not_mem_nullIdeal G B hq
  exact ⟨scalarPlusJ_eq_boundedUniformTwoClosure G,
    (uniformTracialCompletion_identification G hr).2.2.2.2,
    hmemJ, hnotB,
    norm_coronaClass B.toBlockObstruction,
    coronaClass_not_mem_traceZeroSpace B.toBlockObstruction,
    hasUniformTwoDiscontinuousTracialState_of_jordan G B hq hJ huniq⟩

end

end STW22Assembly
end GroupApproximation
