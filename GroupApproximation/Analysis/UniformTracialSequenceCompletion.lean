import GroupApproximation.Analysis.CStarProductCorona
import GroupApproximation.Analysis.HNNTraceTracialStateContinuous

/-!
# The sequence model for a unitized uniform-tracial completion

This file isolates the part of the proposed Problem XXII construction which
does not use projective bundles or trace separation.  The coordinate algebras
are arbitrary unital C-star algebras.  A `UniformTwoGauge` records only the
elementary properties of the coordinate uniform two-seminorm which are used
by the sequence argument.

The two relevant sets of bounded sequences are defined literally:

* `unitizedC0Sum D` consists of the sequences converging in operator norm to
  one scalar sequence;
* `scalarPlusTwoNull G` consists of the sequences converging in the displayed
  coordinate two-gauges to one scalar sequence.

Thus there is no implicit completion object in the statements below.  The
main truncation theorem proves directly that every element of the second set
is uniformly two-approximated by elements of the first.  The converse is
recorded in the same exact tail formulation.

The last section constructs the norm-one tails used to witness discontinuity.
Their classes in the `c₀` corona are all equal, while they converge uniformly
to zero for the displayed two-gauges.
-/

namespace GroupApproximation
namespace UniformTracialSequenceCompletion

open Filter PolarLiftingGeneralCStar
open scoped ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)]

/-- The elementary part of a coordinate uniform two-seminorm.

`zero` and `le_norm` are all that truncation and norm-null inclusion need.
The concrete uniform tracial two-norm has these properties.  Keeping this
small structure separate prevents any unproved Cauchy-completeness or trace
classification statement from entering the sequence calculation. -/
structure UniformTwoGauge (D : ℕ → Type u) [∀ n, CStarAlgebra (D n)] where
  q : ∀ n, D n → ℝ
  zero : ∀ n, q n 0 = 0
  nonneg : ∀ n x, 0 ≤ q n x
  le_norm : ∀ n x, q n x ≤ ‖x‖

/-! ## The gauge coming from all tracial states -/

/-- The actual uniform tracial two-size on one coordinate algebra.  It is the
supremum over all bundled tracial states, not an externally supplied norm. -/
def tracialTwoSize (n : ℕ) (x : D n) : ℝ :=
  sSup (Set.range fun tau : TracialState (D n) ↦
    Real.sqrt ((tau (star x * x)).re))

private theorem sqrt_re_tracialState_star_mul_self_le_norm
    {n : ℕ} (tau : TracialState (D n)) (x : D n) :
    Real.sqrt ((tau (star x * x)).re) ≤ ‖x‖ := by
  have hre0 : 0 ≤ (tau (star x * x)).re :=
    (Complex.nonneg_iff.mp (tau.map_star_mul_self_nonneg x)).1
  have hreNorm : (tau (star x * x)).re ≤ ‖tau (star x * x)‖ :=
    Complex.re_le_norm _
  have hcontract :=
    Manuscript.MFRecognition.TensorSynchronization.norm_tracialState_le
      tau (star x * x)
  have hreSq : (tau (star x * x)).re ≤ ‖x‖ ^ 2 := by
    calc
      (tau (star x * x)).re ≤ ‖tau (star x * x)‖ := hreNorm
      _ ≤ ‖star x * x‖ := hcontract
      _ = ‖x‖ ^ 2 := by rw [CStarRing.norm_star_mul_self, pow_two]
  rw [Real.sqrt_le_iff]
  exact ⟨norm_nonneg x, by simpa [Real.sq_sqrt hre0] using hreSq⟩

/-- The trace-defined supremum is bounded by the operator norm. -/
theorem tracialTwoSize_le_norm [∀ n, Nonempty (TracialState (D n))]
    (n : ℕ) (x : D n) : tracialTwoSize n x ≤ ‖x‖ := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨tau, rfl⟩
  exact sqrt_re_tracialState_star_mul_self_le_norm tau x

/-- The trace-defined supremum is nonnegative. -/
theorem tracialTwoSize_nonneg [∀ n, Nonempty (TracialState (D n))]
    (n : ℕ) (x : D n) : 0 ≤ tracialTwoSize n x := by
  let tau : TracialState (D n) := Classical.choice inferInstance
  have hbound : BddAbove (Set.range fun sigma : TracialState (D n) ↦
      Real.sqrt ((sigma (star x * x)).re)) := by
    refine ⟨‖x‖, ?_⟩
    rintro _ ⟨sigma, rfl⟩
    exact sqrt_re_tracialState_star_mul_self_le_norm sigma x
  exact (Real.sqrt_nonneg _).trans
    (le_csSup hbound (Set.mem_range_self tau))

/-- The actual uniform tracial two-size vanishes at zero. -/
@[simp] theorem tracialTwoSize_zero [∀ n, Nonempty (TracialState (D n))]
    (n : ℕ) : tracialTwoSize n (0 : D n) = 0 := by
  apply le_antisymm
  · simpa using tracialTwoSize_le_norm (D := D) n (0 : D n)
  · exact tracialTwoSize_nonneg (D := D) n 0

/-- The concrete gauge used by the uniform tracial completion, obtained from
all tracial states on every block. -/
def allTracesUniformTwoGauge [∀ n, Nonempty (TracialState (D n))] :
    UniformTwoGauge D where
  q := tracialTwoSize
  zero := tracialTwoSize_zero
  nonneg := tracialTwoSize_nonneg
  le_norm := tracialTwoSize_le_norm

/-- A bounded sequence which converges in norm to a scalar sequence.  This is
the concrete realization of the unitization of the `c₀`-sum. -/
def unitizedC0Sum (D : ℕ → Type u) [∀ n, CStarAlgebra (D n)]
    [∀ n, Nontrivial (D n)] : Set (BoundedCStarSequence D) :=
  {x | ∃ c : ℂ,
    Tendsto (fun n ↦ ‖x n - algebraMap ℂ (D n) c‖) atTop (nhds 0)}

/-- The literal sequence set `ℂ1 + J`, where `J` is the bounded coordinate
sequence whose displayed uniform two-size tends to zero. -/
def scalarPlusTwoNull (G : UniformTwoGauge D) :
    Set (BoundedCStarSequence D) :=
  {x | ∃ c : ℂ,
    Tendsto (fun n ↦ G.q n (x n - algebraMap ℂ (D n) c)) atTop (nhds 0)}

/-- Operator-norm nullity implies nullity for every gauge bounded by the
operator norm.  Hence the unitized `c₀`-sum lies in `ℂ1 + J`. -/
theorem unitizedC0Sum_subset_scalarPlusTwoNull (G : UniformTwoGauge D) :
    unitizedC0Sum D ⊆ scalarPlusTwoNull G := by
  rintro x ⟨c, hx⟩
  refine ⟨c, squeeze_zero'
    (Eventually.of_forall fun n ↦ G.nonneg n _)
    (Eventually.of_forall fun n ↦ G.le_norm n _) hx⟩

/-- Keep the first `N+1` coordinates and put zero afterwards. -/
def truncate (x : BoundedCStarSequence D) (N : ℕ) :
    BoundedCStarSequence D :=
  ⟨fun n ↦ if n ≤ N then x n else 0,
    (lp.memℓp x).mono' fun n ↦ by
      split_ifs
      · exact le_rfl
      · simp⟩

@[simp]
theorem truncate_apply (x : BoundedCStarSequence D) (N n : ℕ) :
    truncate x N n = if n ≤ N then x n else 0 := rfl

/-- Truncate the perturbation of the scalar `λ`, rather than the whole
sequence.  The result is exactly `x n` through coordinate `N` and exactly
`λ 1` afterwards. -/
def scalarTruncation (x : BoundedCStarSequence D) (c : ℂ) (N : ℕ) :
    BoundedCStarSequence D :=
  algebraMap ℂ (BoundedCStarSequence D) c +
    truncate (x - algebraMap ℂ (BoundedCStarSequence D) c) N

@[simp]
theorem scalarTruncation_apply (x : BoundedCStarSequence D) (c : ℂ)
    (N n : ℕ) :
    scalarTruncation x c N n =
      if n ≤ N then x n else algebraMap ℂ (D n) c := by
  change algebraMap ℂ (D n) c +
      (if n ≤ N then x n - algebraMap ℂ (D n) c else 0) = _
  split_ifs <;> simp_all

/-- Every scalar truncation lies in the unitized `c₀`-sum. -/
theorem scalarTruncation_mem_unitizedC0Sum
    (x : BoundedCStarSequence D) (c : ℂ) (N : ℕ) :
    scalarTruncation x c N ∈ unitizedC0Sum D := by
  refine ⟨c, ?_⟩
  apply tendsto_atTop_of_eventually_const (i₀ := N + 1)
  intro n hn
  rw [scalarTruncation_apply]
  simp [show ¬n ≤ N by omega]

/-- Scalar truncation does not enlarge the operator norm beyond the larger of
the norm of the original bounded sequence and the scalar tail.  This is the
operator-norm boundedness needed in the *bounded* uniform-two completion. -/
theorem norm_scalarTruncation_le_max
    (x : BoundedCStarSequence D) (c : ℂ) (N : ℕ) :
    ‖scalarTruncation x c N‖ ≤ max ‖x‖ ‖c‖ := by
  rw [lp.norm_eq_ciSup]
  apply ciSup_le
  intro n
  rw [scalarTruncation_apply]
  split_ifs
  · exact (boundedCStarSequence_coord_norm_le D x n).trans (le_max_left _ _)
  · simpa only [norm_algebraMap, norm_one, mul_one] using
      (le_max_right ‖x‖ ‖c‖)

/-- A point is boundedly uniformly two-approximable from `S` if it is the
uniform coordinate-gauge limit of a single operator-norm bounded sequence in
`S`.  This is the sequence-level notion used in the bounded uniform-tracial
completion; it deliberately does not assert that the gauge is a global norm. -/
def IsBoundedUniformTwoApproximable (G : UniformTwoGauge D)
    (S : Set (BoundedCStarSequence D)) (x : BoundedCStarSequence D) : Prop :=
  ∃ a : ℕ → BoundedCStarSequence D,
    (∀ k, a k ∈ S) ∧
    (∃ C : ℝ, ∀ k, ‖a k‖ ≤ C) ∧
    ∀ ε > 0, ∃ N, ∀ k, N ≤ k → ∀ n,
      G.q n (x n - a k n) < ε

/-- After the truncation point, the coordinate error is exactly the original
perturbation of the scalar. -/
theorem q_sub_scalarTruncation_of_lt (G : UniformTwoGauge D)
    (x : BoundedCStarSequence D) (c : ℂ) {N n : ℕ} (hN : N < n) :
    G.q n (x n - scalarTruncation x c N n) =
      G.q n (x n - algebraMap ℂ (D n) c) := by
  rw [scalarTruncation_apply]
  simp [show ¬n ≤ N by omega]

/-- Before the truncation point, the coordinate error is zero. -/
theorem q_sub_scalarTruncation_of_le (G : UniformTwoGauge D)
    (x : BoundedCStarSequence D) (c : ℂ) {N n : ℕ} (hn : n ≤ N) :
    G.q n (x n - scalarTruncation x c N n) = 0 := by
  rw [scalarTruncation_apply]
  simp [hn, G.zero]

/-- The exact uniform tail approximation statement.  This is the density
half of the identification of the bounded sequence completion with
`ℂ1 + J`: each two-null scalar perturbation has scalar truncations in the
unitized `c₀`-sum, and one truncation controls *all* later coordinates. -/
theorem scalarTruncations_uniformly_approximate
    (G : UniformTwoGauge D) {x : BoundedCStarSequence D}
    (hx : x ∈ scalarPlusTwoNull G) :
    ∃ c : ℂ,
      (∀ N, scalarTruncation x c N ∈ unitizedC0Sum D) ∧
      ∀ ε > 0, ∃ N, ∀ n, N < n →
        G.q n (x n - scalarTruncation x c N n) < ε := by
  obtain ⟨c, hx⟩ := hx
  refine ⟨c, fun N ↦ scalarTruncation_mem_unitizedC0Sum x c N, ?_⟩
  intro ε hε
  have hev : ∀ᶠ n in atTop,
      G.q n (x n - algebraMap ℂ (D n) c) < ε :=
    (Metric.tendsto_nhds.mp hx) ε hε |>.mono fun n hn ↦ by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (G.nonneg n _)] using hn
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [q_sub_scalarTruncation_of_lt G x c hn]
  exact hN n hn.le

/-- The bounded-density half of the concrete completion identification.
Every element of `ℂ1 + J` is represented by its scalar truncations in the
unitized `c₀`-sum; those truncations have one uniform operator-norm bound and
their gauge error tends to zero uniformly over *all* coordinates. -/
theorem scalarTruncations_bounded_uniformly_approximate
    (G : UniformTwoGauge D) {x : BoundedCStarSequence D}
    (hx : x ∈ scalarPlusTwoNull G) :
    ∃ c : ℂ,
      (∀ N, scalarTruncation x c N ∈ unitizedC0Sum D) ∧
      (∀ N, ‖scalarTruncation x c N‖ ≤ max ‖x‖ ‖c‖) ∧
      ∀ ε > 0, ∃ N, ∀ k, N ≤ k → ∀ n,
        G.q n (x n - scalarTruncation x c k n) < ε := by
  obtain ⟨c, hx⟩ := hx
  refine ⟨c, fun N ↦ scalarTruncation_mem_unitizedC0Sum x c N,
    fun N ↦ norm_scalarTruncation_le_max x c N, ?_⟩
  intro ε hε
  have hev : ∀ᶠ n in atTop,
      G.q n (x n - algebraMap ℂ (D n) c) < ε :=
    (Metric.tendsto_nhds.mp hx) ε hε |>.mono fun n hn ↦ by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (G.nonneg n _)] using hn
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun k hk n ↦ ?_⟩
  by_cases hn : n ≤ k
  · rw [q_sub_scalarTruncation_of_le G x c hn]
    exact hε
  · rw [q_sub_scalarTruncation_of_lt G x c (Nat.lt_of_not_ge hn)]
    exact hN n (hk.trans (Nat.le_of_lt (Nat.lt_of_not_ge hn)))

/-- Consequently, the concrete set `ℂ1 + J` is contained in the bounded
uniform-two sequential closure of the unitized `c₀`-sum. -/
theorem scalarPlusTwoNull_subset_boundedUniformTwoApproximable
    (G : UniformTwoGauge D) :
    scalarPlusTwoNull G ⊆
      {x | IsBoundedUniformTwoApproximable G (unitizedC0Sum D) x} := by
  intro x hx
  obtain ⟨c, hmem, hbound, hconv⟩ :=
    scalarTruncations_bounded_uniformly_approximate G hx
  exact ⟨fun N ↦ scalarTruncation x c N, hmem,
    ⟨max ‖x‖ ‖c‖, hbound⟩, hconv⟩

/-- Conversely, the uniform tail condition is exactly membership in
`ℂ1 + J`.  This packages the nontrivial quantifier direction without naming
an ambient completion which has not been constructed. -/
theorem mem_scalarPlusTwoNull_iff_uniform_tail
    (G : UniformTwoGauge D) (x : BoundedCStarSequence D) :
    x ∈ scalarPlusTwoNull G ↔
      ∃ c : ℂ, ∀ ε > 0, ∃ N, ∀ n, N < n →
        G.q n (x n - scalarTruncation x c N n) < ε := by
  constructor
  · intro hx
    obtain ⟨c, -, htail⟩ := scalarTruncations_uniformly_approximate G hx
    exact ⟨c, htail⟩
  · rintro ⟨c, htail⟩
    refine ⟨c, Metric.tendsto_nhds.2 ?_⟩
    intro ε hε
    obtain ⟨N, hN⟩ := htail ε hε
    filter_upwards [eventually_gt_atTop N] with n hn
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (G.nonneg n (x n - algebraMap ℂ (D n) c))]
    simpa only [q_sub_scalarTruncation_of_lt G x c hn] using hN n hn

/-! ## Tails and the norm corona -/

/-- Delete the first `N+1` coordinates of a bounded sequence. -/
def tail (x : BoundedCStarSequence D) (N : ℕ) :
    BoundedCStarSequence D :=
  x - truncate x N

@[simp]
theorem tail_apply (x : BoundedCStarSequence D) (N n : ℕ) :
    tail x N n = if n ≤ N then 0 else x n := by
  change x n - (if n ≤ N then x n else 0) = _
  split_ifs <;> simp_all

/-- Removing finitely many coordinates does not change a class in the norm
`c₀` corona. -/
theorem corona_tail_eq (x : BoundedCStarSequence D) (N : ℕ) :
    cStarProductCoronaQuotient D atTop (tail x N) =
      cStarProductCoronaQuotient D atTop x := by
  rw [← sub_eq_zero]
  rw [← map_sub]
  apply (cStarProductCoronaQuotient_eq_zero_iff D atTop _).2
  rw [IsNullCStarSequence]
  apply tendsto_atTop_of_eventually_const (i₀ := N + 1)
  intro n hn
  have hnot : ¬n ≤ N := by omega
  simp [tail_apply, hnot]

/-- Coordinatewise two-nullity makes the deleted-prefix tails converge to
zero *uniformly over all coordinates*.  This is the precise convergence used
to exhibit a discontinuous functional. -/
theorem tails_uniformly_two_null (G : UniformTwoGauge D)
    (x : BoundedCStarSequence D)
    (hx : Tendsto (fun n ↦ G.q n (x n)) atTop (nhds 0)) :
    ∀ ε > 0, ∃ N, ∀ n,
      G.q n (tail x N n) < ε := by
  intro ε hε
  have hev : ∀ᶠ n in atTop, G.q n (x n) < ε :=
    (Metric.tendsto_nhds.mp hx) ε hε |>.mono fun n hn ↦ by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (G.nonneg n _)] using hn
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  refine ⟨K, fun n ↦ ?_⟩
  by_cases hn : n ≤ K
  · rw [tail_apply]
    simp [hn, G.zero, hε]
  · rw [tail_apply]
    simp only [hn, ↓reduceIte]
    exact hK n (Nat.le_of_lt (Nat.lt_of_not_ge hn))

/-- The quotient norm of a sequence is the limsup of its coordinate norms.
This specializes the genuine C-star quotient norm theorem to the `c₀`
corona used here. -/
theorem norm_corona_eq_limsup (x : BoundedCStarSequence D) :
    ‖cStarProductCoronaQuotient D atTop x‖ =
      Filter.limsup (fun n ↦ ‖x n‖) atTop :=
  norm_cStarProductCorona_quotient_eq_limsup D atTop x

/-- A functional on the norm corona which detects `x` has the same nonzero
value on every tail, although those tails converge uniformly to zero in the
two-gauges.  This is an unconditional discontinuity certificate; no
Cuntz--Pedersen separation theorem is assumed here. -/
theorem tail_discontinuity_certificate (G : UniformTwoGauge D)
    (x : BoundedCStarSequence D)
    (hx : Tendsto (fun n ↦ G.q n (x n)) atTop (nhds 0))
    (φ : CStarProductCorona D atTop → ℂ)
    (hφ : φ (cStarProductCoronaQuotient D atTop x) ≠ 0) :
    (∀ N, φ (cStarProductCoronaQuotient D atTop (tail x N)) =
      φ (cStarProductCoronaQuotient D atTop x)) ∧
    (∀ ε > 0, ∃ N, ∀ n, G.q n (tail x N n) < ε) ∧
    φ (cStarProductCoronaQuotient D atTop x) ≠ 0 := by
  refine ⟨fun N ↦ congrArg φ (corona_tail_eq x N),
    tails_uniformly_two_null G x hx, hφ⟩

end

end UniformTracialSequenceCompletion
end GroupApproximation
