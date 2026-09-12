import GroupApproximation.Analysis.CStarProductCorona
import GroupApproximation.Analysis.ShulmanTraceClasses

/-!
# Unbounded self-commutator width survives the norm corona

This file formalizes the analytic core of the counterexample to automatic
trace continuity in a uniform tracial completion.  The geometric input is
kept in the exact form supplied by the Chern-class argument: at stage `n`, an
element `h n` of norm one is at distance at least one from every sum of at
most `n` self-commutators.

The main theorem proves that the class of `(h n)` in the norm corona is not in
the Cuntz--Pedersen trace-zero space.  In particular, no choice of a fixed
finite number of self-commutators can approximate it in the quotient.  This
is the quantifier passage used in the proposed negative solution to Problem
XXII; the proof uses the genuine quotient C-star norm and its `limsup`
formula, not an algebraic proxy for the quotient.

The construction of the homogeneous blocks
`Γ(End(1 ⊕ L_n^⊕n))` and the Chern-class proof of the finite-stage hypothesis
belong to the geometric input.  Mathlib currently has neither the required
section C-star algebra nor the relevant Chern-class API, so that input is an
explicit field of `BlockObstruction` rather than an undeclared axiom.
-/

namespace GroupApproximation
namespace CuntzPedersenCoronaObstruction

open Filter PolarLiftingGeneralCStar
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

universe u

/-- The additive self-commutator `[z*,z] = z*z - z*z*`. -/
def selfCommutator {C : Type*} [Ring C] [Star C] (z : C) : C :=
  star z * z - z * star z

@[simp]
theorem selfCommutator_apply {C : Type*} [Ring C] [Star C] (z : C) :
    selfCommutator z = star z * z - z * star z := rfl

/-- The exact finite-stage output of the Chern-class compression argument.

For the intended block at stage `n ≥ 1`, `h n = p_n-q_n`.  The norm-one
clause makes `(h n)` a bounded sequence.  `width` says that `h n` stays at
distance at least one from every sum of `ell` self-commutators whenever
`ell ≤ n`; this is precisely the conclusion obtained by the common zero of
the `L_n^⊕n`-valued lower-left corners. -/
structure BlockObstruction (D : ℕ → Type u) [∀ n, CStarAlgebra (D n)] where
  h : ∀ n, D n
  norm_h : ∀ n, ‖h n‖ = 1
  selfadjoint_h : ∀ n, star (h n) = h n
  width : ∀ (ell n : ℕ), ell ≤ n → ∀ z : Fin ell → D n,
    1 ≤ ‖h n - ∑ j, selfCommutator (z j)‖

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)]

/-- The bounded sequence represented by the obstructing elements. -/
def BlockObstruction.sequence (B : BlockObstruction D) :
    BoundedCStarSequence D :=
  ⟨B.h, memℓp_infty ⟨1, by
    rintro _ ⟨n, rfl⟩
    simpa using (B.norm_h n).le⟩⟩

@[simp]
theorem BlockObstruction.sequence_apply (B : BlockObstruction D) (n : ℕ) :
    B.sequence n = B.h n := rfl

/-- The obstructing class in the `c₀` norm corona. -/
def BlockObstruction.coronaClass (B : BlockObstruction D) :
    CStarProductCorona D atTop :=
  cStarProductCoronaQuotient D atTop B.sequence

/-- Finite sums of self-commutators, with the number of summands exposed as
data.  Taking the closure of this set is the Cuntz--Pedersen trace-zero
space. -/
def IsFiniteSelfCommutatorSum {C : Type*} [Ring C] [Star C] (x : C) : Prop :=
  ∃ ell : ℕ, ∃ z : Fin ell → C, x = ∑ j, selfCommutator (z j)

/-- The norm closure of the finite sums of self-commutators. -/
def traceZeroSpace (C : Type*) [TopologicalSpace C] [Ring C] [Star C] : Set C :=
  closure {x | IsFiniteSelfCommutatorSum x}

private theorem coordinate_selfCommutator
    (z : BoundedCStarSequence D) (n : ℕ) :
    selfCommutator z n = selfCommutator (z n) := rfl

private theorem coordinate_sum {ell : ℕ}
    (z : Fin ell → BoundedCStarSequence D) (n : ℕ) :
    (∑ j, z j) n = ∑ j, z j n := by
  let ev : BoundedCStarSequence D →+ D n :=
    { toFun := fun x ↦ x n
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change ev (∑ j, z j) = ∑ j, ev (z j)
  exact map_sum ev (fun j ↦ z j) Finset.univ

private theorem quotient_selfCommutator
    (z : BoundedCStarSequence D) :
    cStarProductCoronaQuotient D atTop (selfCommutator z) =
      selfCommutator (cStarProductCoronaQuotient D atTop z) := by
  simp [selfCommutator]

/-- A fixed finite number of quotient self-commutators remains at distance
at least one from the obstructing class.  This is the formal `limsup` version
of choosing a sufficiently large stage `n ≥ ell` in the paper proof. -/
theorem norm_coronaClass_sub_sum_selfCommutator_ge_one
    (B : BlockObstruction D) (ell : ℕ)
    (z : Fin ell → BoundedCStarSequence D) :
    1 ≤ ‖B.coronaClass -
      ∑ j, selfCommutator
        (cStarProductCoronaQuotient D atTop (z j))‖ := by
  let w : BoundedCStarSequence D :=
    B.sequence - ∑ j, selfCommutator (z j)
  have hquot :
      B.coronaClass -
          ∑ j, selfCommutator
            (cStarProductCoronaQuotient D atTop (z j)) =
        cStarProductCoronaQuotient D atTop w := by
    simp only [BlockObstruction.coronaClass, w, map_sub, map_sum,
      quotient_selfCommutator]
  rw [hquot, norm_cStarProductCorona_quotient_eq_limsup]
  apply le_limsup_of_frequently_le
  · exact (eventually_ge_atTop ell).frequently.mono fun n hn ↦ by
      have hw : w n = B.h n - ∑ j, selfCommutator (z j n) := by
        dsimp only [w]
        change B.sequence n - (∑ j, selfCommutator (z j)) n =
          B.h n - ∑ j, selfCommutator (z j n)
        rw [BlockObstruction.sequence_apply, coordinate_sum]
        apply congrArg (B.h n - ·)
        apply Finset.sum_congr rfl
        intro j _
        exact coordinate_selfCommutator (z j) n
      rw [hw]
      exact B.width ell n hn (fun j ↦ z j n)
  · exact ⟨‖w‖, show ∀ᶠ n : ℕ in atTop, ‖w n‖ ≤ ‖w‖ from
      Eventually.of_forall fun n ↦ boundedCStarSequence_coord_norm_le D w n⟩

/-- The same lower bound for finite self-commutator sums already presented
as elements of the quotient.  Surjectivity of the quotient map supplies one
bounded representative for each of the finitely many summands. -/
theorem norm_coronaClass_sub_ge_one_of_finiteSum
    (B : BlockObstruction D) {x : CStarProductCorona D atTop}
    (hx : IsFiniteSelfCommutatorSum x) :
    1 ≤ ‖B.coronaClass - x‖ := by
  obtain ⟨ell, y, rfl⟩ := hx
  choose z hz using fun j ↦
    cStarProductCoronaQuotient_surjective D atTop (y j)
  rw [show (∑ j, selfCommutator (y j)) =
      ∑ j, selfCommutator
        (cStarProductCoronaQuotient D atTop (z j)) by
    apply Finset.sum_congr rfl
    intro j _
    rw [hz j]]
  exact norm_coronaClass_sub_sum_selfCommutator_ge_one B ell z

/-- **The quotient obstruction.**  The class of `(h n)` does not belong to
the Cuntz--Pedersen trace-zero space of the norm corona. -/
theorem coronaClass_not_mem_traceZeroSpace (B : BlockObstruction D) :
    B.coronaClass ∉ traceZeroSpace (CStarProductCorona D atTop) := by
  intro hmem
  obtain ⟨x, hx, hdist⟩ :=
    Metric.mem_closure_iff.mp hmem (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
  have hlower := norm_coronaClass_sub_ge_one_of_finiteSum B hx
  rw [dist_eq_norm] at hdist
  linarith

/-- The obstructing corona class has norm exactly one. -/
theorem norm_coronaClass (B : BlockObstruction D) : ‖B.coronaClass‖ = 1 := by
  rw [BlockObstruction.coronaClass,
    norm_cStarProductCorona_quotient_eq_limsup]
  have hfun : (fun n ↦ ‖B.sequence n‖) = fun _ : ℕ ↦ (1 : ℝ) := by
    funext n
    exact B.norm_h n
  rw [hfun, limsup_const]

/-- The sequence is self-adjoint coordinatewise. -/
theorem star_sequence (B : BlockObstruction D) : star B.sequence = B.sequence := by
  ext n
  exact B.selfadjoint_h n

/-- Hence its class in the norm corona is self-adjoint. -/
theorem star_coronaClass (B : BlockObstruction D) :
    star B.coronaClass = B.coronaClass := by
  rw [BlockObstruction.coronaClass, ← map_star,
    star_sequence B]

/-! ## The tracially null rate and Cuntz--Pedersen separation -/

/-- The extra information carried by the projective-space blocks: the
obstruction has vanishing uniform `2`-size and is killed by every fibre trace.

For `D n = Γ(End(1 ⊕ L_{n+1}^{⊕(n+1)}))`, the intended `twoSize` is the
supremum of the normalized fibre Hilbert--Schmidt norms and

`twoSize n (h n) = sqrt (2 / (n+2))`.

The convergence proof is elementary once that equality has been established;
the structure records the invariant statement actually used by completion.
-/
structure TraciallyNullObstruction (D : ℕ → Type u)
    [∀ n, CStarAlgebra (D n)] extends BlockObstruction D where
  twoSize : ∀ n, D n → ℝ
  twoSize_h_tendsto_zero : Tendsto (fun n ↦ twoSize n (h n)) atTop (nhds 0)
  trace_h : ∀ (n : ℕ) (τ : TracialState (D n)), τ (h n) = 0

/-- A bounded sequence is null for a displayed family of uniform `2`-sizes. -/
def IsUniformTwoNull (q : ∀ n, D n → ℝ) (x : BoundedCStarSequence D) : Prop :=
  Tendsto (fun n ↦ q n (x n)) atTop (nhds 0)

/-- The obstructing sequence is uniformly `2`-null. -/
theorem TraciallyNullObstruction.sequence_isUniformTwoNull
    (B : TraciallyNullObstruction D) :
    IsUniformTwoNull B.twoSize B.toBlockObstruction.sequence := by
  unfold IsUniformTwoNull
  change Tendsto (fun n ↦ B.twoSize n (B.h n)) atTop (nhds 0)
  exact B.twoSize_h_tendsto_zero

/-- The same sequence is not operator-norm null.  Thus it belongs to the
uniform-`2` tail ideal but not to the original `c₀` ideal. -/
theorem TraciallyNullObstruction.sequence_not_isNullCStarSequence
    (B : TraciallyNullObstruction D) :
    ¬ IsNullCStarSequence D atTop B.toBlockObstruction.sequence := by
  intro hnull
  have hnorm : Tendsto (fun n ↦ ‖B.h n‖) atTop (nhds 0) := by
    simpa only [IsNullCStarSequence, BlockObstruction.sequence_apply] using hnull
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 0) := by
    convert hnorm using 1
    funext n
    exact (B.norm_h n).symm
  have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have : (0 : ℝ) = 1 := tendsto_nhds_unique hone hconst
  norm_num at this

/-- Every designated finite-stage tracial state annihilates the obstructing
coordinate. -/
theorem TraciallyNullObstruction.fibre_trace_sequence
    (B : TraciallyNullObstruction D) (n : ℕ) (τ : TracialState (D n)) :
    τ (B.toBlockObstruction.sequence n) = 0 := by
  rw [BlockObstruction.sequence_apply]
  exact B.trace_h n τ

/-- Delete the first `N+1` coordinates of the obstructing sequence. -/
def BlockObstruction.tail (B : BlockObstruction D) (N : ℕ) :
    BoundedCStarSequence D :=
  ⟨fun n ↦ if N < n then B.h n else 0,
    memℓp_infty ⟨1, by
      rintro _ ⟨n, rfl⟩
      change ‖if N < n then B.h n else 0‖ ≤ 1
      split_ifs
      · simpa using (B.norm_h n).le
      · simp⟩⟩

@[simp]
theorem BlockObstruction.tail_apply (B : BlockObstruction D) (N n : ℕ) :
    B.tail N n = if N < n then B.h n else 0 := rfl

/-- Removing a finite prefix does not change the norm-corona class. -/
theorem BlockObstruction.quotient_tail (B : BlockObstruction D) (N : ℕ) :
    cStarProductCoronaQuotient D atTop (B.tail N) = B.coronaClass := by
  rw [BlockObstruction.coronaClass, cStarProductCoronaQuotient_apply,
    cStarProductCoronaQuotient_apply,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  change IsNullCStarSequence D atTop (B.tail N - B.sequence)
  rw [IsNullCStarSequence]
  apply (tendsto_congr' ?_).mpr tendsto_const_nhds
  filter_upwards [eventually_gt_atTop N] with n hn
  simp [BlockObstruction.tail_apply, hn]

/-- Any corona trace detecting the obstruction takes the same nonzero value
on every tail.  Combined with a tail `2`-norm estimate, this is the explicit
discontinuity sequence from the counterexample. -/
theorem tracialState_tail_eq
    (B : BlockObstruction D)
    (σ : TracialState (CStarProductCorona D atTop)) (N : ℕ) :
    σ (cStarProductCoronaQuotient D atTop (B.tail N)) = σ B.coronaClass := by
  rw [B.quotient_tail N]

/-- The separation form of the Cuntz--Pedersen theorem used by the argument.
It is stated as a property so the substantial general theorem is visible in
the dependency surface until it is added to Mathlib. -/
def HasCuntzPedersenSeparation (C : Type*) [CStarAlgebra C] : Prop :=
  ∀ x : C, star x = x → x ∉ traceZeroSpace C →
    ∃ τ : TracialState C, τ x ≠ 0

/-- Cuntz--Pedersen separation turns the corona obstruction into a tracial
state which detects it. -/
theorem exists_tracialState_detecting_coronaClass
    (B : BlockObstruction D)
    (hCP : HasCuntzPedersenSeparation (CStarProductCorona D atTop)) :
    ∃ τ : TracialState (CStarProductCorona D atTop), τ B.coronaClass ≠ 0 :=
  hCP B.coronaClass (star_coronaClass B)
    (coronaClass_not_mem_traceZeroSpace B)

/-- Every tracial state takes the scalar `λ1` to `λ`. -/
theorem tracialState_map_algebraMap
    {C : Type*} [Ring C] [StarRing C] [Algebra ℂ C]
    (τ : TracialState C) (c : ℂ) : τ (algebraMap ℂ C c) = c := by
  rw [Algebra.algebraMap_eq_smul_one, τ.map_smul, τ.apply_one, smul_eq_mul,
    mul_one]

/-- The exact quotient conclusion used for Problem XXII.  If the canonical
uniform trace kills the obstructing class, Cuntz--Pedersen supplies a second
trace.  Both traces agree on the scalar quotient of the original unitized
`c₀`-sum, while their values on the `2`-null class differ. -/
theorem exists_distinct_tracialState_agree_on_scalars
    (B : BlockObstruction D)
    (hCP : HasCuntzPedersenSeparation (CStarProductCorona D atTop))
    (τu : TracialState (CStarProductCorona D atTop))
    (hτu : τu B.coronaClass = 0) :
    ∃ σ : TracialState (CStarProductCorona D atTop),
      σ B.coronaClass ≠ τu B.coronaClass ∧
      ∀ c : ℂ, σ (algebraMap ℂ (CStarProductCorona D atTop) c) =
        τu (algebraMap ℂ (CStarProductCorona D atTop) c) := by
  obtain ⟨σ, hσ⟩ := exists_tracialState_detecting_coronaClass B hCP
  refine ⟨σ, ?_, fun c ↦ ?_⟩
  · rw [hτu]
    exact hσ
  · rw [tracialState_map_algebraMap σ, tracialState_map_algebraMap τu]

end

end CuntzPedersenCoronaObstruction
end GroupApproximation
