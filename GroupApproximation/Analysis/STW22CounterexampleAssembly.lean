import GroupApproximation.Analysis.CoronaCoordinateStateCompactness
import GroupApproximation.Analysis.UniformTracialBoundedCauchyQuotient
import GroupApproximation.Analysis.CuntzPedersenTraceZero

/-!
# Sections 5--7 of the STW Problem XXII counterexample audit, assembled

The audit's endgame is assembled here from landed pieces, along the
**compactness** route rather than the Cuntz--Pedersen/Jordan route:

* **(A14)**  `Analysis/CoronaCoordinateStateCompactness` turns *arbitrarily
  late coordinate-state solvability* into a tracial state `sigma` on the `c₀`
  corona with `sigma hbar = 1`.  Finitely many state constraints are solved at
  one sufficiently late coordinate, and Banach--Alaoglu assembles the actual
  tracial state.  No Jordan decomposition and no Cuntz--Pedersen separation is
  used anywhere below.
* **(A15)**  `sigma` pulls back along `M ↪ ∏_s D_s → H` to a tracial state
  `sigma_tilde` of the uniform tracial completion `M = ℂ1 + J`, and its
  restriction to `A = ℂ1 + B` is the extreme trace at infinity.
* **(A16)--(A18)**  `sigma_tilde` takes the value one on every tail truncation
  `h^(N)`, while the uniform two-norms of those tails tend to zero.  So
  `sigma_tilde` is a tracial state of `M` which is not continuous for the
  gauge, i.e. `T(A) ⊊ T(M)`.

## The corrected obstruction input

The printed argument zeroes only the lower-left blocks `c_j` at a common point.
That is enough for the *norm* obstruction (A2), but it is **not** enough to make
the vector state at that point tracial on the finite family: the compression
computation leaves the `b_j` terms.  Both off-diagonal blocks `b_j` **and**
`c_j` must be zeroed simultaneously.  The hypothesis bundle
`CoordinateStateBlockData` therefore records, in place of a norm-distance
`width` clause, exactly what the corrected geometry delivers:

`ArbitrarilyLateCoordinateStateConstraints seq` --- for every finite family of
bounded sequences and every floor, some coordinate past that floor carries a
state which sends `seq` there to one and kills the displayed self-commutators.

Two things about that bundle are worth stating plainly.  It needs neither
`‖h_s‖ = 1` nor self-adjointness of `h_s`: `CoordinateStateBlockData.not_isNull`
derives `h ∉ B` from the coordinate states alone.  And it *proves* the audit's
(A13), `hbar ∉ H₀`, rather than assuming a width bound --- see
`coronaClass_not_mem_traceZeroSpace_of_blockData`.

## The corona used

The audit forms `H = M/B`.  This file uses the corona `(∏_s D_s)/B` of the whole
bounded product together with the composite `M ↪ ∏_s D_s → (∏_s D_s)/B`, which
is what the landed compactness theorem speaks about.  The resulting tracial
state restricts along that composite to `sigma_tilde`, which is exactly the
audit's state.

## The completion is the honest one

`Analysis/UniformTracialBoundedCauchyQuotient` builds the bounded uniform-two
Cauchy quotient of `A` and transports a C-star structure onto it across the
proved bijection with `ℂ1 + J`.  The endpoint is therefore stated twice: on the
concrete star subalgebra `scalarPlusJSubalgebra G`, and transported along the
landed `realizationStarAlgEquiv` to the completion object itself.

## The alternative route

`Analysis/CuntzPedersenJordanTracial` reaches the same detecting trace from a
norm-distance obstruction, Hahn--Banach and the Jordan decomposition.  Nothing
here depends on it; it is recorded only as the alternative, and it carries two
unproved literature hypotheses which the compactness route does not need.

## The block model

The intended coordinate algebras are the antipodally covariant matrix functions
of `Analysis/AntipodalHomogeneousBlock`: `D s := RealProjectiveBlock d s`, the
fixed-point algebra of `C(S^d, M_(s+1))` under conjugation by the diagonal
involution, which models `Γ(End(1 ⊕ λ_ℂ^{⊕s}))` over `RP^d` with no bundle
library.  Everything below is generic in `D`, so that instantiation is a
substitution.

`STW22CounterexampleAssemblyModelTest` model-tests every `Prop` introduced here.
-/

namespace GroupApproximation
namespace STW22Assembly

open Filter PolarLiftingGeneralCStar
open UniformTracialSequenceCompletion UniformTracialTwoNullIdeal
open UniformTracialCompletionIdentification UniformTracialBoundedCauchyQuotient
open CuntzPedersenCoronaObstruction CuntzPedersenTraceZero
open CStarState CoronaCoordinateStateCompactness

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)]

/-! ## The uniform two-norm

Hostile check 2 of the audit: for a positive element the supremum of the tracial
two-norms over `T(A) = Prob(K)` is attained on point masses, so the uniform
two-norm is the supremum of the coordinate gauges.  That supremum is taken as
the definition here, which keeps the statement independent of the still
unformalized identification `T(A) = Prob(K)`. -/

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

/-! ## Scalar parts cancel in self-commutators

The coordinate-state constraints are quantified over arbitrary bounded
sequences, so they already cover every lift of an element of `H = M/B`.  The
lemmas here record why: a lift `λ1 + z` contributes the same self-commutator as
its ideal part `z`, so no separate clause for scalars is needed. -/

/-- Expansion of `(c·1 + y)⋆ (c·1 + y)`, the one algebraic step behind the
cancellation. -/
private theorem star_expand_smul_one_add {C : Type*} [CStarAlgebra C] (c : ℂ)
    (y : C) :
    star (c • (1 : C) + y) * (c • (1 : C) + y) =
      (star c * c) • (1 : C) + (star c • y + c • star y) + star y * y := by
  have e1 : (star c • (1 : C)) * (c • (1 : C)) = (star c * c) • (1 : C) := by
    rw [smul_mul_assoc, one_mul, smul_smul]
  have e2 : (star c • (1 : C)) * y = star c • y := by
    rw [smul_mul_assoc, one_mul]
  have e3 : star y * (c • (1 : C)) = c • star y := by
    rw [mul_smul_comm, mul_one]
  rw [star_add, star_smul, star_one, add_mul, mul_add, mul_add, e1, e2, e3]
  abel

/-- Adding a scalar multiple of the unit leaves a self-commutator unchanged. -/
theorem selfCommutator_smul_one_add {C : Type*} [CStarAlgebra C] (c : ℂ)
    (y : C) : selfCommutator (c • (1 : C) + y) = selfCommutator y := by
  have hs : star (c • (1 : C) + y) = star c • (1 : C) + star y := by
    rw [star_add, star_smul, star_one]
  have hsw : star (star c • (1 : C) + star y) = c • (1 : C) + y := by
    rw [star_add, star_smul, star_one, star_star, star_star]
  have h1 := star_expand_smul_one_add c y
  have h2 := star_expand_smul_one_add (star c) (star y)
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

/-! ## The corrected block input -/

/-- **(A10) from the coordinate states alone.**  A sequence carrying
arbitrarily late coordinate-state constraints is not null, so its corona class
is nonzero.  No norm-one clause is needed: a tracial state of the corona cannot
send the class of a null sequence to one. -/
theorem not_isNull_of_arbitrarilyLateCoordinateStates
    {h : BoundedCStarSequence D}
    (hcoord : ArbitrarilyLateCoordinateStateConstraints h) :
    h ∉ nullCStarSequenceIdeal D atTop := by
  intro hnull
  obtain ⟨σ, hσ⟩ :=
    exists_corona_tracialState_of_arbitrarilyLate_coordinate_states h hcoord
  rw [(cStarProductCoronaQuotient_eq_zero_iff D atTop h).2 hnull,
    σ.map_zero] at hσ
  exact zero_ne_one hσ

/-- **The obstruction data for the compactness route.**

`seq` is the audit's `h = (h_s)`.  `gauge_tendsto_zero` is (A1), which puts `h`
in the ideal `J`.  `coordinate_states` replaces the audit's norm-distance clause
(A2) by what the corrected geometry actually supplies: at arbitrarily late
coordinates a single state detects `h` and annihilates any prescribed finite
family of self-commutators.

Producing that state is where the printed argument had to be corrected.
Zeroing only the lower-left blocks `c_j` of the `z_j` at a common point of
`RP^d` gives the compression bound of (A2), but the corner of `[z_j*, z_j]`
still carries `-b_j b_j*`, so the vector state at that point is not tracial on
the family.  Both `b_j` and `c_j` must vanish at the chosen point; the
common-zero input is applied to the lower-left corners of `z_j` and of
`star z_j` together, and then the vector state works.

Nothing here asks for `‖h_s‖ = 1` or for `h_s` to be self-adjoint.  The intended
blocks have both, but `not_isNull` below derives `h ∉ B` from the coordinate
states alone. -/
structure CoordinateStateBlockData (E : ℕ → Type u) [∀ n, CStarAlgebra (E n)]
    [∀ n, Nontrivial (E n)] (G : TracialTwoGauge E) where
  /-- The obstructing bounded sequence `h = (h_s)`. -/
  seq : BoundedCStarSequence E
  /-- (A1): the coordinate gauges tend to zero, so `h ∈ J`. -/
  gauge_tendsto_zero : Tendsto (fun n ↦ G.q n (seq n)) atTop (nhds 0)
  /-- The corrected geometric input, replacing the printed (A2). -/
  coordinate_states : ArbitrarilyLateCoordinateStateConstraints seq

namespace CoordinateStateBlockData

variable {G : TracialTwoGauge D}

/-- (A1) restated: the obstruction lies in the uniform two-null ideal `J`. -/
theorem mem_twoNullIdeal (B : CoordinateStateBlockData D G) :
    B.seq ∈ twoNullIdeal G :=
  B.gauge_tendsto_zero

/-- **(A14).**  The compactness theorem produces a tracial state of the corona
taking the value one on the obstructing class.  No Jordan decomposition and no
Cuntz--Pedersen separation enters. -/
theorem exists_corona_tracialState (B : CoordinateStateBlockData D G) :
    ∃ σ : TracialState (CStarProductCorona D atTop),
      σ (cStarProductCoronaQuotient D atTop B.seq) = 1 :=
  exists_corona_tracialState_of_arbitrarilyLate_coordinate_states
    B.seq B.coordinate_states

/-- **(A10).**  The obstruction is not in the `c₀`-sum `B`, so its corona class
is nonzero.  This needs no norm-one clause: a state on the corona cannot send a
null sequence to one. -/
theorem not_isNull (B : CoordinateStateBlockData D G) :
    B.seq ∉ nullCStarSequenceIdeal D atTop :=
  not_isNull_of_arbitrarilyLateCoordinateStates B.coordinate_states

/-- The corona class is nonzero. -/
theorem coronaClass_ne_zero (B : CoordinateStateBlockData D G) :
    cStarProductCoronaQuotient D atTop B.seq ≠ 0 := by
  intro hzero
  exact B.not_isNull
    ((cStarProductCoronaQuotient_eq_zero_iff D atTop B.seq).1 hzero)

end CoordinateStateBlockData

/-- **(A13), proved rather than assumed.**  The compactness route reaches the
Cuntz--Pedersen conclusion from the other side: the detecting trace annihilates
the trace-zero space, so the obstructing class is outside it.  The alternative
route obtains this from a norm-distance bound and then needs Cuntz--Pedersen
separation to go back; here no separation theorem is used. -/
theorem coronaClass_not_mem_traceZeroSpace_of_blockData
    {G : TracialTwoGauge D} (B : CoordinateStateBlockData D G) :
    cStarProductCoronaQuotient D atTop B.seq ∉
      traceZeroSpace (CStarProductCorona D atTop) := by
  obtain ⟨σ, hσ⟩ := B.exists_corona_tracialState
  refine not_mem_traceZeroSpace_of_tracialState_ne_zero σ ?_
  rw [hσ]
  exact one_ne_zero

/-! ## `M = ℂ1 + J`, the quotient map, and the pullback state -/

/-- The ideal `J` sits inside `M = ℂ1 + J`. -/
theorem twoNullIdeal_le_scalarPlusJ (G : TracialTwoGauge D)
    {x : BoundedCStarSequence D} (hx : x ∈ twoNullIdeal G) :
    x ∈ scalarPlusJ G :=
  ⟨0, x, hx, by rw [map_zero, zero_add]⟩

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

/-- **(A15) on `A`.**  The pullback kills the `c₀`-sum `B`, so on `A = ℂ1 + B`
it is the extreme trace `tau_infinity` coming from the scalar quotient: an
element of `M` whose distance to the scalar `c` is norm-null is sent to `c`. -/
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

/-- The same statement in the coordinate form in which
`A = unitization(⊕_s D_s)` is realized: if the coordinates of `x` converge in
operator norm to the scalar `c`, the pullback takes the value `c` at `x`. -/
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
    (B : CoordinateStateBlockData D G) (N : ℕ) :
    tail B.seq N ∈ twoNullIdeal G := by
  rw [mem_twoNullIdeal_iff]
  refine squeeze_zero' (Eventually.of_forall fun n ↦ G.nonneg n _)
    (Eventually.of_forall fun n ↦ ?_) B.gauge_tendsto_zero
  rw [tail_apply]
  split_ifs
  · rw [G.zero]
    exact G.nonneg n (B.seq n)
  · exact le_rfl

/-- The tails of the obstruction lie in `M = ℂ1 + J`. -/
theorem tail_mem_scalarPlusJ (G : TracialTwoGauge D)
    (B : CoordinateStateBlockData D G) (N : ℕ) :
    tail B.seq N ∈ scalarPlusJ G :=
  twoNullIdeal_le_scalarPlusJ G (tail_mem_twoNullIdeal G B N)

/-- **(A17).**  The uniform two-norms of the tails tend to zero.  This is the
uniform-over-coordinates form of the audit's `sup_{s ≥ n} sqrt (2/(s+1))`, with
no rate assumed. -/
theorem uniformTwoNorm_tail_tendsto_zero (G : TracialTwoGauge D)
    (B : CoordinateStateBlockData D G) :
    Tendsto (fun N ↦ uniformTwoNorm G (tail B.seq N)) atTop (nhds 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  have hev : ∀ᶠ n in atTop, G.q n (B.seq n) < ε / 2 :=
    ((Metric.tendsto_nhds.mp B.gauge_tendsto_zero) (ε / 2)
      (half_pos hε)).mono fun n hn ↦ by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (G.nonneg n _)] using hn
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  filter_upwards [eventually_ge_atTop K] with N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (uniformTwoNorm_nonneg G _)]
  have hbd : uniformTwoNorm G (tail B.seq N) ≤ ε / 2 := by
    refine uniformTwoNorm_le G _ fun n ↦ ?_
    rw [tail_apply]
    split_ifs with hn
    · rw [G.zero]
      linarith
    · exact (hK n (by omega)).le
  linarith

/-! ## The endpoint -/

/-- Sequential continuity at zero, for the uniform two-norm, of a tracial state
of `M = ℂ1 + J`.

Every tracial state of `A` extends to `M` with this property, by construction of
the uniform tracial completion.  STW Problem XXII asks whether every tracial
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

/-- The negation of continuity is exactly a uniformly two-null sequence in `M`
along which the state does not tend to zero. -/
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

/-- **(A14)--(A18) with no literature hypothesis.**  From the corrected block
data alone:

1. the compactness theorem supplies a tracial state `sigma` of the corona with
   `sigma hbar = 1`;
2. its pullback `sigma_tilde` to `M` takes the value one on every tail `h^(N)`,
   because removing a finite prefix does not move the corona class;
3. those tails are uniformly two-null.

So `sigma_tilde` is a tracial state of `M` which is not continuous for the
gauge. -/
theorem hasUniformTwoDiscontinuousTracialState_of_blockData
    (G : TracialTwoGauge D) (B : CoordinateStateBlockData D G) :
    HasUniformTwoDiscontinuousTracialState G := by
  obtain ⟨σ, hσ⟩ := B.exists_corona_tracialState
  refine ⟨pullbackTracialState G σ, ?_⟩
  refine not_isUniformTwoContinuous_of_constant_value G (pullbackTracialState G σ)
    (fun N ↦ ⟨tail B.seq N, tail_mem_scalarPlusJ G B N⟩)
    one_ne_zero (fun N ↦ ?_) (uniformTwoNorm_tail_tendsto_zero G B)
  show σ (cStarProductCoronaQuotient D atTop (tail B.seq N)) = 1
  rw [corona_tail_eq]
  exact hσ

/-! ## Transport to the honest completion object -/

/-- Pull a tracial state of `M = ℂ1 + J` back to the bounded uniform-two Cauchy
completion of `A`, along the landed star-algebra equivalence. -/
def completionTracialState (G : TracialTwoGauge D) {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison G r)
    (σ : TracialState ↥(scalarPlusJSubalgebra G)) :
    TracialState (BoundedUniformTwoCompletion G r hr) :=
  σ.compStarAlgHom (realizationStarAlgEquiv G hr).toStarAlgHom

@[simp] theorem completionTracialState_apply (G : TracialTwoGauge D)
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison G r)
    (σ : TracialState ↥(scalarPlusJSubalgebra G))
    (x : BoundedUniformTwoCompletion G r hr) :
    completionTracialState G hr σ x = σ (realize G hr x) := rfl

/-- Audit pin: the bounded uniform-two Cauchy completion of `A` is a genuine
C-star algebra, so the tracial states below are tracial states of the honest
completion object and not of a stand-in. -/
theorem boundedUniformTwoCompletion_hasCStarAlgebra (G : TracialTwoGauge D)
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison G r) :
    Nonempty (CStarAlgebra (BoundedUniformTwoCompletion G r hr)) :=
  ⟨inferInstance⟩

/-- **The endpoint on the completion object.**  The discontinuous tracial state
of `M` transports along `realizationStarAlgEquiv` to a tracial state of the
bounded uniform-two Cauchy completion, with the same discontinuity witness read
through the realization map. -/
theorem exists_discontinuous_tracialState_completion (G : TracialTwoGauge D)
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison G r)
    (hM : HasUniformTwoDiscontinuousTracialState G) :
    ∃ (σ : TracialState (BoundedUniformTwoCompletion G r hr))
      (x : ℕ → BoundedUniformTwoCompletion G r hr),
      Tendsto (fun N ↦ uniformTwoNorm G
        ((realize G hr (x N) : BoundedCStarSequence D))) atTop (nhds 0) ∧
      ¬ Tendsto (fun N ↦ σ (x N)) atTop (nhds 0) := by
  obtain ⟨σ, hσ⟩ := hM
  obtain ⟨y, hy2, hyv⟩ := (not_isUniformTwoContinuous_iff G σ).1 hσ
  have hsymm : ∀ N : ℕ,
      realize G hr ((realizationStarAlgEquiv G hr).symm (y N)) = y N :=
    fun N ↦ (realizationStarAlgEquiv G hr).apply_symm_apply (y N)
  refine ⟨completionTracialState G hr σ,
    fun N ↦ (realizationStarAlgEquiv G hr).symm (y N), ?_, ?_⟩
  · have hfun : (fun N ↦ uniformTwoNorm G
        ((realize G hr ((realizationStarAlgEquiv G hr).symm (y N)) :
          BoundedCStarSequence D)))
        = fun N ↦ uniformTwoNorm G ((y N : BoundedCStarSequence D)) := by
      funext N
      rw [hsymm N]
    rw [hfun]
    exact hy2
  · have hfun : (fun N ↦ completionTracialState G hr σ
        ((realizationStarAlgEquiv G hr).symm (y N)))
        = fun N ↦ σ (y N) := by
      funext N
      rw [completionTracialState_apply, hsymm N]
    rw [hfun]
    exact hyv

/-! ## The summary -/

/-- **Sections 5--7 of the audit in one statement.**

The hypotheses are exactly the unproved inputs, all named and all visible:

* `G` and `hr`, the coordinate two-gauge with the finite-rank comparison
  `‖a‖ ≤ r s ‖a‖_{2,s}` of Section 4;
* `B`, the corrected block data of `CoordinateStateBlockData`, whose only
  substantial field is the arbitrarily-late coordinate-state solvability that
  the antipodal blocks are to supply.

No Jordan decomposition, no Cuntz--Pedersen separation, and no norm-distance
width bound is assumed.

The conclusions are, in order: (A8), the identification of `M = ℂ1 + J` with the
bounded uniform two-closure of `A`; that the Cauchy completion of `A` is a
C-star algebra; (A1)/(A10), `h ∈ J \ B`; (A14), the detecting corona trace;
(A13), which is now proved rather than assumed; (A18) on `M`; and (A18)
transported to the completion object. -/
theorem stw22_trace_problem_counterexample
    (G : TracialTwoGauge D) {r : ℕ → ℝ} (hr : IsCoordinateNormComparison G r)
    (B : CoordinateStateBlockData D G) :
    scalarPlusJ G =
        {x : BoundedCStarSequence D |
          IsBoundedUniformTwoApproximable G.toUniformTwoGauge
            (unitizedC0Sum D) x} ∧
      Nonempty (CStarAlgebra (BoundedUniformTwoCompletion G r hr)) ∧
      B.seq ∈ twoNullIdeal G ∧
      B.seq ∉ nullCStarSequenceIdeal D atTop ∧
      (∃ σ : TracialState (CStarProductCorona D atTop),
        σ (cStarProductCoronaQuotient D atTop B.seq) = 1) ∧
      cStarProductCoronaQuotient D atTop B.seq ∉
        traceZeroSpace (CStarProductCorona D atTop) ∧
      HasUniformTwoDiscontinuousTracialState G ∧
      (∃ (σ : TracialState (BoundedUniformTwoCompletion G r hr))
        (x : ℕ → BoundedUniformTwoCompletion G r hr),
        Tendsto (fun N ↦ uniformTwoNorm G
          ((realize G hr (x N) : BoundedCStarSequence D))) atTop (nhds 0) ∧
        ¬ Tendsto (fun N ↦ σ (x N)) atTop (nhds 0)) :=
  ⟨scalarPlusJ_eq_boundedUniformTwoClosure G,
    boundedUniformTwoCompletion_hasCStarAlgebra G hr,
    B.mem_twoNullIdeal, B.not_isNull, B.exists_corona_tracialState,
    coronaClass_not_mem_traceZeroSpace_of_blockData B,
    hasUniformTwoDiscontinuousTracialState_of_blockData G B,
    exists_discontinuous_tracialState_completion G hr
      (hasUniformTwoDiscontinuousTracialState_of_blockData G B)⟩

end

end STW22Assembly
end GroupApproximation
