import GroupApproximation.Analysis.NormMatrixCorona
import GroupApproximation.Analysis.PreliminaryInequalitiesPrinted
import GroupApproximation.Sofic.UltrafilterLimit

/-!
# The tracial matrix ultraproduct and its ultratrace

`Analysis/NormMatrixCorona.lean` divides the C-star algebra
`ℓ∞(M_{X n}(ℂ))` of uniformly operator-norm-bounded matrix sequences by the
sequences whose *operator* norms vanish along a filter.  This file divides the
same numerator by the sequences whose *normalized Hilbert--Schmidt* norms
vanish, which is a strictly larger ideal -- a rank-one projection in `M_d(ℂ)`
has operator norm `1` and Hilbert--Schmidt norm `d^{-1/2}` -- and therefore a
genuinely different quotient.  At a free ultrafilter `ω` the quotient is the
manuscript's tracial ultraproduct

`Mω = ∏_ω M_{X n}(ℂ) = ℓ∞(M_{X n}) / J₂ω`,   `J₂ω = {a : lim_ω ‖a n‖₂ = 0}`,

and it carries the ultratrace `trω [a] = lim_ω tr_{X n}(a n)`.

## What is proved

* `hilbertSchmidtNullIdeal` is a two-sided, adjoint-stable ideal, and
  `isClosed_hilbertSchmidtNullIdeal` says it is closed for the *uniform
  operator norm* of the numerator.  Closedness is what makes the quotient a
  normed -- not merely seminormed -- ring.
* `TracialMatrixQuotient` carries the quotient norm, and is a complete normed
  ring with an isometric involution, compatible with its complex algebra
  structure.
* `ultratrace` is the descended `lim_ω tr`.  It is additive, complex
  homogeneous (`ultratrace_smul`), tracial (`ultratrace_mul_comm`),
  `*`-compatible (`ultratrace_star`), contractive (`norm_ultratrace_le`),
  positive and normalized (`ultratrace_star_mul_self_nonneg`,
  `ultratrace_one`), and **faithful**
  (`ultratrace_star_mul_self_eq_zero_iff`).  The first five together say it is
  a tracial state on `Mω`.

Faithfulness is not an extra argument: the identity `‖A‖₂² = tr(AᴴA)` makes
`trω (x* x)` literally the ultralimit of the squared Hilbert--Schmidt norms of
any lift, and that limit vanishes exactly when the lift lies in the ideal that
was divided out.  This is `ultratrace_star_mul_self_eq_ofReal` followed by
`seqHSLimit_eq_zero_iff`.

## The estimates that make the ideal an ideal

Three printed inequalities do all the work and are taken from the corpus
rather than reproved: `hsNormSq_mul_le_sq_l2_opNorm_mul` and
`hsNormSq_mul_le_sq_l2_opNorm_right` (`‖AB‖₂ ≤ ‖A‖‖B‖₂` and
`‖AB‖₂ ≤ ‖B‖‖A‖₂`, in squared form), and
`PrelimNotation.hsNormSq_le_sq_l2_opNorm` (`‖A‖₂ ≤ ‖A‖`).  Additivity of the
ideal and its closedness use only the crude squared triangle inequality
`hsNormSq_add_le`, `|A+B|₂² ≤ 2|A|₂² + 2|B|₂²`; a factor `2` per step is
harmless because the number of steps is fixed before the accuracy is chosen,
and this avoids introducing a second `NormedAddCommGroup` structure on
`Matrix (X n) (X n) ℂ` alongside the scoped `L2Operator` one.

## What is deliberately *not* claimed

The quotient is **not** given a `CStarRing` instance *in this file*; the
identity is proved in `Analysis/TracialQuotientCStarIdentity.lean`, and the
instances and the exact quotient-norm formula live in
`Analysis/TracialQuotientCStar.lean`.  The C-star identity for
a quotient of a C-star algebra by a closed two-sided ideal is not formal: it
needs an approximate unit of the ideal, and mathlib (at the pinned revision)
has no quotient C-star instance to inherit.  Unlike the operator-norm corona
of `NormMatrixCorona`, whose quotient norm is the concrete limsup
`lim_ω ‖a n‖` and for which the identity is a coordinatewise computation, the
`‖·‖₂`-quotient norm here has no such formula: it is a genuine infimum.  The
missing step is exactly

> for `j ∈ J₂ω` and `ε > 0` there is `e ∈ J₂ω` with `0 ≤ e ≤ 1` and
> `‖j - j e‖ < ε`,

**The matrix-level half of that step is built**, in
`Analysis/HilbertSchmidtApproximateUnit.exists_projection_approximate_unit`.
For a single matrix `j` and a threshold `t > 0` it produces an orthogonal
projection `e` with `‖e‖ ≤ 1`, `‖j - j e‖² ≤ t` and `t · ‖e‖₂² ≤ ‖j‖₂²`: it
thresholds the spectrum of `jᴴj`, so the order bounds come free from
idempotence and `‖e‖₂² = rank / d` is a trace identity, Chebyshev supplying
the second clause.

Note what that is and is not.  It is a statement about **one matrix**, not
about a member of `J₂ω`.  The sequence-level step quoted above is no longer
open: `Analysis/TracialQuotientCStar.exists_ideal_approximate_unit` performs
it -- the projections chosen coordinatewise, and the second clause -- `t`
fixed before the sequence varies, so `t · ‖eₙ‖₂² ≤ ‖jₙ‖₂²` forces
`‖eₙ‖₂ → 0` along any filter along which `‖jₙ‖₂ → 0` -- read along the
filter to put `e` back in the ideal.  That assembly, the instances it
unlocks, and the formula `‖a + J‖ = inf { ‖a - a e‖ : e ∈ J }` all live in
that file; the matrix lemma is their main ingredient rather than their
conclusion.

*An alternative construction, recorded but **not built**.*  In the ambient
algebra one may instead take the resolvent

`e = a * (δ • 1 + a)⁻¹`,   `a = star j * j`,

which is a *continuous* function of `a`, namely `t ↦ t / (δ + t)`, so it needs
only the functional calculus of a nonnegative element and never forms an
eigenbasis.  Its appeal is at the sequence level: membership `e ∈ J₂ω` is
`Ideal.mul_mem_right` -- `a ∈ J₂ω` because `j` is, and `e` is `a` times an
ambient element -- so the argument never needs the (unavailable) theory of
ideals as non-unital C-star algebras, whereas the projection witness carries a
pointwise Chebyshev bound across the filter.  The two estimates would be one
step each: `‖e‖₂ ≤ ‖a‖₂ / δ` from `‖AB‖₂ ≤ ‖B‖ ‖A‖₂` together with
`‖(δ + a)⁻¹‖ ≤ 1/δ`, and `‖a‖₂ ≤ ‖j‖ ‖j‖₂ → 0`; while
`‖j (1 - e)‖² = ‖(1 - e) a (1 - e)‖ = ‖g(a)‖` with `g t = t δ² / (δ + t)²`,
whose supremum on `[0,∞)` is `δ/4`, gives `‖j (1 - e)‖ ≤ √δ / 2`.  Mathlib's
`Analysis/CStarAlgebra/ApproximateUnit.lean` is built around this same
function in the form `x ↦ 1 - (1 + x)⁻¹`
(`CFC.monotoneOn_one_sub_one_add_inv`, `norm_cfcₙ_one_sub_one_add_inv_lt_one`).
The assembly has since been done through the projection witness instead
(`Analysis/TracialQuotientCStar.lean`, up to the exact `sInf` formula); the
resolvent construction stays unbuilt prose.

A note on the search that established the premise: the claim that the pinned
mathlib has no quotient C-star instance is not an inference from failing to
find one.  All sixteen `CStarRing` instances in the pin were enumerated --
`ContinuousMapZero`, `C(α,β)`, `α →ᵇ β`, `C₀(α,β)`, `Quaternion`, `E →L[𝕜] E`,
`ℝ`, `Prod`, `Pi`, `Pi'`, `Eᵐᵒᵖ`, `Multiplier`, `CStarMatrix`, `RCLike`,
`Unitization`, `lp B ∞` -- and not one is a quotient, an ideal or a
subalgebra.

Nothing below papers over the gap: no statement here asserts the C-star
identity for the quotient norm.
-/

/- Typeclass search on `↥(ModelBoundedSequence X) ⧸ hilbertSchmidtNullIdeal X l`
has to unfold the ideal quotient, then `lp`, and then rediscover the
`Fintype`/`DecidableEq` instances of each model through the `FiniteModel`
projections.  `NormMatrixCorona` avoids this by carrying its index types as
instance-implicit section variables; here the index sequence is a
`FiniteModel`-valued function -- which is what the Hilbert--Schmidt norm needs
-- so the search is genuinely longer and does not fit the default budget. -/
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1000000

/- The nonemptiness of the models is a standing hypothesis of the whole
construction (without it the numerator is not a unital ring), but a dozen
coordinatewise estimates do not mention it.  Threading `omit` through them
moves the unused frontier one declaration at a time rather than removing it,
so the linter is turned off for the file instead. -/
set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace TracialUltraproduct

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## Two conveniences for nonnegative real families -/

section RealTendsto

variable {α : Type*} {l : Filter α} {g : α → ℝ}

/-- A nonnegative family is null along `l` as soon as it is eventually below
every positive threshold. -/
theorem tendsto_zero_of_forall_eventually_lt (hg0 : ∀ x, 0 ≤ g x)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, g x < ε) :
    Tendsto g l (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h ε hε] with x hx
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hg0 x)]
  exact hx

/-- The converse direction, in the form every call site below wants. -/
theorem eventually_lt_of_tendsto_zero (h : Tendsto g l (nhds 0)) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ x in l, g x < ε := by
  filter_upwards [(Metric.tendsto_nhds.mp h) ε hε] with x hx
  rw [Real.dist_eq, sub_zero] at hx
  exact (le_abs_self (g x)).trans_lt hx

end RealTendsto

/-! ## Elementary Hilbert--Schmidt and normalized-trace facts

None of these is in the corpus; each is a one-step consequence of a
declaration that is. -/

/-- The normalized Hilbert--Schmidt norm squares to `hsNormSq`. -/
theorem sq_hsNorm (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    hsNorm Y A ^ 2 = hsNormSq Y A := by
  unfold hsNorm
  exact Real.sq_sqrt (hsNormSq_nonneg Y A)

theorem hsNormSq_zero (Y : FiniteModel) :
    hsNormSq Y (0 : Matrix Y Y ℂ) = 0 := by
  unfold hsNormSq
  simp

theorem hsNorm_zero (Y : FiniteModel) : hsNorm Y (0 : Matrix Y Y ℂ) = 0 := by
  unfold hsNorm
  rw [hsNormSq_zero, Real.sqrt_zero]

/-- **`‖A‖₂² = tr_r(Aᴴ A)`.**  The corpus records the identity in the order
`A Aᴴ`; the order used by a positive element `x* x` is this one. -/
theorem ofReal_hsNormSq_conjTranspose_mul (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    ((hsNormSq Y A : ℝ) : ℂ) = normTrace Y (Aᴴ * A) := by
  have h := ofReal_hsNormSq Y Aᴴ
  rw [Matrix.conjTranspose_conjTranspose, hsNormSq_conjTranspose] at h
  exact h

theorem normTrace_zero (Y : FiniteModel) :
    normTrace Y (0 : Matrix Y Y ℂ) = 0 := by
  show Matrix.trace (0 : Matrix Y Y ℂ) / _ = 0
  rw [Matrix.trace_zero, zero_div]

theorem normTrace_add (Y : FiniteModel) (A B : Matrix Y Y ℂ) :
    normTrace Y (A + B) = normTrace Y A + normTrace Y B := by
  show Matrix.trace (A + B) / _ = _
  rw [Matrix.trace_add, add_div]
  rfl

theorem normTrace_smul (Y : FiniteModel) (c : ℂ) (A : Matrix Y Y ℂ) :
    normTrace Y (c • A) = c * normTrace Y A := by
  show Matrix.trace (c • A) / _ = _
  rw [Matrix.trace_smul, smul_eq_mul, mul_div_assoc]
  rfl

/-- **Traciality of the normalized trace**, from cyclicity of `Matrix.trace`. -/
theorem normTrace_mul_comm (Y : FiniteModel) (A B : Matrix Y Y ℂ) :
    normTrace Y (A * B) = normTrace Y (B * A) := by
  show Matrix.trace (A * B) / _ = Matrix.trace (B * A) / _
  rw [Matrix.trace_mul_comm]

/-- The normalized trace is `*`-compatible: the normalization is a real
scalar, so it commutes with conjugation. -/
theorem normTrace_conjTranspose (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    normTrace Y Aᴴ = (starRingEnd ℂ) (normTrace Y A) := by
  show Matrix.trace Aᴴ / ((Fintype.card Y : ℕ) : ℂ)
      = (starRingEnd ℂ) (Matrix.trace A / ((Fintype.card Y : ℕ) : ℂ))
  rw [Matrix.trace_conjTranspose, map_div₀, Complex.conj_natCast]
  rfl

/-! ## The numerator -/

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (l : Filter ℕ)

/-- The uniformly operator-norm-bounded matrix sequences over a sequence of
finite models.  This is the numerator of `NormMatrixCorona`, read at a
`FiniteModel`-valued index sequence.

The models are required to be nonempty -- the manuscript's "positive
dimensional" -- and not for convenience: `lp.inftyRing` needs
`NormOneClass (Matrix (X n) (X n) ℂ)`, and `‖1‖ = 1` fails for the empty
model, where the identity matrix is `0`.  Without it the numerator is not even
a unital ring. -/
abbrev ModelBoundedSequence := BoundedMatrixSequence (fun n ↦ X n)

omit [∀ n, Nonempty (X n)] in
/-- Every coordinate Hilbert--Schmidt norm is bounded by the uniform operator
norm: `‖a n‖₂ ≤ ‖a n‖ ≤ ‖a‖`. -/
theorem hsNorm_coord_le (a : ModelBoundedSequence X) (n : ℕ) :
    hsNorm (X n) (a n) ≤ ‖a‖ :=
  (PrelimNotation.hsNorm_le_l2_opNorm (X n) (a n)).trans
    (boundedMatrixSequence_coord_norm_le (fun n ↦ X n) a n)

omit [∀ n, Nonempty (X n)] in
/-- The squared form of the same bound. -/
theorem hsNormSq_coord_le (a : ModelBoundedSequence X) (n : ℕ) :
    hsNormSq (X n) (a n) ≤ ‖a‖ ^ 2 := by
  refine (PrelimNotation.hsNormSq_le_sq_l2_opNorm (X n) (a n)).trans ?_
  have h := boundedMatrixSequence_coord_norm_le (fun n ↦ X n) a n
  rw [pow_two, pow_two]
  exact mul_self_le_mul_self (norm_nonneg (a n)) h

/-! ## The Hilbert--Schmidt null ideal -/

/-- A bounded matrix sequence is `‖·‖₂`-null along `l` when its *normalized*
Hilbert--Schmidt norms tend to zero along `l`.  At a free ultrafilter this is
the manuscript's `lim_ω ‖a n‖₂ = 0`. -/
def IsHilbertSchmidtNull (a : ModelBoundedSequence X) : Prop :=
  Tendsto (fun n ↦ hsNorm (X n) (a n)) l (nhds 0)

omit [∀ n, Nonempty (X n)] in
/-- Every estimate below is cheaper in squared form, and squaring is
reversible on nonnegative families. -/
theorem isHilbertSchmidtNull_iff_sq (a : ModelBoundedSequence X) :
    IsHilbertSchmidtNull X l a ↔
      Tendsto (fun n ↦ hsNormSq (X n) (a n)) l (nhds 0) := by
  constructor
  · intro h
    have h0 : Tendsto (fun n ↦ hsNorm (X n) (a n)) l (nhds 0) := h
    have h2 := h0.pow 2
    rw [show ((0 : ℝ) ^ 2) = 0 by norm_num] at h2
    refine h2.congr fun n ↦ ?_
    exact sq_hsNorm (X n) (a n)
  · intro h
    have hc : Tendsto Real.sqrt (nhds (0 : ℝ)) (nhds 0) :=
      Real.continuous_sqrt.tendsto' 0 0 Real.sqrt_zero
    have hcomp : Tendsto (fun n ↦ hsNorm (X n) (a n)) l (nhds 0) :=
      (hc.comp h).congr fun n ↦ rfl
    exact hcomp

omit [∀ n, Nonempty (X n)] in
/-- The domination criterion used for every closure property of the ideal. -/
theorem isHilbertSchmidtNull_of_sq_le {a : ModelBoundedSequence X} {g : ℕ → ℝ}
    (hg : Tendsto g l (nhds 0))
    (hle : ∀ n, hsNormSq (X n) (a n) ≤ g n) :
    IsHilbertSchmidtNull X l a := by
  rw [isHilbertSchmidtNull_iff_sq]
  exact squeeze_zero' (Eventually.of_forall fun n ↦ hsNormSq_nonneg (X n) (a n))
    (Eventually.of_forall hle) hg

namespace IsHilbertSchmidtNull

omit [∀ n, Nonempty (X n)] in
theorem zero : IsHilbertSchmidtNull X l 0 := by
  rw [IsHilbertSchmidtNull]
  refine tendsto_const_nhds.congr fun n ↦ ?_
  exact (hsNorm_zero (X n)).symm

omit [∀ n, Nonempty (X n)] in
theorem add {a b : ModelBoundedSequence X}
    (ha : IsHilbertSchmidtNull X l a) (hb : IsHilbertSchmidtNull X l b) :
    IsHilbertSchmidtNull X l (a + b) := by
  rw [isHilbertSchmidtNull_iff_sq] at ha hb
  refine isHilbertSchmidtNull_of_sq_le X l
    (g := fun n ↦ 2 * hsNormSq (X n) (a n) + 2 * hsNormSq (X n) (b n)) ?_ ?_
  · have h : Tendsto
        (fun n ↦ 2 * hsNormSq (X n) (a n) + 2 * hsNormSq (X n) (b n)) l
        (nhds ((2 : ℝ) * 0 + (2 : ℝ) * 0)) :=
      (tendsto_const_nhds.mul ha).add (tendsto_const_nhds.mul hb)
    rw [show ((2 : ℝ) * 0 + (2 : ℝ) * 0) = 0 by norm_num] at h
    exact h
  · intro n
    exact hsNormSq_add_le (X n) (a n) (b n)

omit [∀ n, Nonempty (X n)] in
theorem mul_left (b : ModelBoundedSequence X) {a : ModelBoundedSequence X}
    (ha : IsHilbertSchmidtNull X l a) : IsHilbertSchmidtNull X l (b * a) := by
  rw [isHilbertSchmidtNull_iff_sq] at ha
  refine isHilbertSchmidtNull_of_sq_le X l
    (g := fun n ↦ ‖b‖ ^ 2 * hsNormSq (X n) (a n)) ?_ ?_
  · have h : Tendsto (fun n ↦ ‖b‖ ^ 2 * hsNormSq (X n) (a n)) l
        (nhds (‖b‖ ^ 2 * 0)) := tendsto_const_nhds.mul ha
    rw [mul_zero] at h
    exact h
  · intro n
    have hb : ‖b n‖ ≤ ‖b‖ :=
      boundedMatrixSequence_coord_norm_le (fun n ↦ X n) b n
    have hstep : hsNormSq (X n) (b n * a n) ≤ ‖b n‖ ^ 2 * hsNormSq (X n) (a n) :=
      hsNormSq_mul_le_sq_l2_opNorm_mul (X n) (b n) (a n)
    have h0 := hsNormSq_nonneg (X n) (a n)
    have hsqle : ‖b n‖ ^ 2 ≤ ‖b‖ ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self (norm_nonneg (b n)) hb
    exact hstep.trans (mul_le_mul_of_nonneg_right hsqle h0)

omit [∀ n, Nonempty (X n)] in
theorem mul_right {a : ModelBoundedSequence X}
    (ha : IsHilbertSchmidtNull X l a) (b : ModelBoundedSequence X) :
    IsHilbertSchmidtNull X l (a * b) := by
  rw [isHilbertSchmidtNull_iff_sq] at ha
  refine isHilbertSchmidtNull_of_sq_le X l
    (g := fun n ↦ ‖b‖ ^ 2 * hsNormSq (X n) (a n)) ?_ ?_
  · have h : Tendsto (fun n ↦ ‖b‖ ^ 2 * hsNormSq (X n) (a n)) l
        (nhds (‖b‖ ^ 2 * 0)) := tendsto_const_nhds.mul ha
    rw [mul_zero] at h
    exact h
  · intro n
    have hb : ‖b n‖ ≤ ‖b‖ :=
      boundedMatrixSequence_coord_norm_le (fun n ↦ X n) b n
    have hstep : hsNormSq (X n) (a n * b n) ≤ ‖b n‖ ^ 2 * hsNormSq (X n) (a n) :=
      hsNormSq_mul_le_sq_l2_opNorm_right (X n) (a n) (b n)
    have h0 := hsNormSq_nonneg (X n) (a n)
    have hsqle : ‖b n‖ ^ 2 ≤ ‖b‖ ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_self_le_mul_self (norm_nonneg (b n)) hb
    exact hstep.trans (mul_le_mul_of_nonneg_right hsqle h0)

omit [∀ n, Nonempty (X n)] in
theorem star {a : ModelBoundedSequence X}
    (ha : IsHilbertSchmidtNull X l a) :
    IsHilbertSchmidtNull X l (Star.star a) := by
  rw [isHilbertSchmidtNull_iff_sq] at ha ⊢
  refine ha.congr fun n ↦ ?_
  have h : (Star.star a) n = (a n)ᴴ := Matrix.star_eq_conjTranspose (a n)
  rw [h, hsNormSq_conjTranspose]

end IsHilbertSchmidtNull

/-- **The ideal `J₂ω`.**  The two-sided ideal of bounded matrix sequences whose
normalized Hilbert--Schmidt norms vanish along `l`. -/
def hilbertSchmidtNullIdeal : Ideal (ModelBoundedSequence X) where
  carrier := {a | IsHilbertSchmidtNull X l a}
  zero_mem' := IsHilbertSchmidtNull.zero X l
  add_mem' := IsHilbertSchmidtNull.add X l
  smul_mem' := fun b _ ha ↦ IsHilbertSchmidtNull.mul_left X l b ha

instance hilbertSchmidtNullIdeal_isTwoSided :
    (hilbertSchmidtNullIdeal X l).IsTwoSided where
  mul_mem_of_left := fun b ha ↦ IsHilbertSchmidtNull.mul_right X l ha b

theorem hilbertSchmidtNullIdeal_star_mem {a : ModelBoundedSequence X}
    (ha : a ∈ hilbertSchmidtNullIdeal X l) :
    star a ∈ hilbertSchmidtNullIdeal X l :=
  IsHilbertSchmidtNull.star X l ha

theorem mem_hilbertSchmidtNullIdeal_iff (a : ModelBoundedSequence X) :
    a ∈ hilbertSchmidtNullIdeal X l ↔ IsHilbertSchmidtNull X l a :=
  Iff.rfl

/-- **The ideal is closed for the uniform operator norm.**  This is the step
that makes the quotient seminorm a norm.  The estimate is the crude squared
triangle inequality applied once, together with `‖A‖₂ ≤ ‖A‖`. -/
theorem isClosed_hilbertSchmidtNullIdeal :
    IsClosed (hilbertSchmidtNullIdeal X l : Set (ModelBoundedSequence X)) := by
  apply IsSeqClosed.isClosed
  intro s a hs hsa
  change IsHilbertSchmidtNull X l a
  rw [isHilbertSchmidtNull_iff_sq]
  refine tendsto_zero_of_forall_eventually_lt
    (fun n ↦ hsNormSq_nonneg (X n) (a n)) ?_
  intro ε hε
  have hquarter : (0 : ℝ) < ε / 4 := by linarith
  have hroot : (0 : ℝ) < Real.sqrt (ε / 4) := Real.sqrt_pos.mpr hquarter
  obtain ⟨k, hk⟩ := ((Metric.tendsto_nhds.mp hsa) _ hroot).exists
  have hd : ‖a - s k‖ < Real.sqrt (ε / 4) := by
    rw [← dist_eq_norm, dist_comm]
    exact hk
  have hsq : ‖a - s k‖ ^ 2 < ε / 4 := by
    have hrt : Real.sqrt (ε / 4) ^ 2 = ε / 4 := Real.sq_sqrt hquarter.le
    have hlt : ‖a - s k‖ * ‖a - s k‖
        < Real.sqrt (ε / 4) * Real.sqrt (ε / 4) :=
      mul_self_lt_mul_self (norm_nonneg _) hd
    rw [pow_two] at hrt ⊢
    linarith
  have hsk : Tendsto (fun n ↦ hsNormSq (X n) (s k n)) l (nhds 0) :=
    (isHilbertSchmidtNull_iff_sq X l (s k)).mp (hs k)
  filter_upwards [eventually_lt_of_tendsto_zero hsk hquarter] with n hn
  have hcoord : ‖a n - s k n‖ ≤ ‖a - s k‖ :=
    boundedMatrixSequence_coord_norm_le (fun n ↦ X n) (a - s k) n
  have hrw : (a n - s k n) + s k n = a n := by abel
  have hstep : hsNormSq (X n) (a n)
      ≤ 2 * hsNormSq (X n) (a n - s k n) + 2 * hsNormSq (X n) (s k n) := by
    have h := hsNormSq_add_le (X n) (a n - s k n) (s k n)
    rwa [hrw] at h
  have hfirst : hsNormSq (X n) (a n - s k n) ≤ ‖a - s k‖ ^ 2 := by
    refine (PrelimNotation.hsNormSq_le_sq_l2_opNorm (X n) (a n - s k n)).trans ?_
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self (norm_nonneg (a n - s k n)) hcoord
  linarith

noncomputable instance hilbertSchmidtNullIdeal_isClosed :
    IsClosed (hilbertSchmidtNullIdeal X l : Set (ModelBoundedSequence X)) :=
  isClosed_hilbertSchmidtNullIdeal X l

/-! ## The quotient -/

/-- **The tracial matrix quotient at the filter `l`.**  At a free ultrafilter
this is the manuscript's tracial ultraproduct `∏_ω M_{X n}(ℂ)`. -/
abbrev TracialMatrixQuotient :=
  ModelBoundedSequence X ⧸ hilbertSchmidtNullIdeal X l

private theorem tracialQuot_exists_rep_norm_lt
    (x : TracialMatrixQuotient X l) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ModelBoundedSequence X,
      Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) a = x ∧ ‖a‖ < ‖x‖ + ε :=
  Submodule.Quotient.norm_mk_lt x hε

private theorem tracialQuot_norm_mk_le (a : ModelBoundedSequence X) :
    ‖Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) a‖ ≤ ‖a‖ :=
  Submodule.Quotient.norm_mk_le (hilbertSchmidtNullIdeal X l) a

/-- The quotient seminorm is submultiplicative.  Mathlib's ideal-quotient
normed-ring instance is commutative; this is the noncommutative analogue, and
the proof is the usual choice of representatives of nearly minimal norm with a
tolerance `δ` calibrated once against `‖x‖ + ‖y‖ + 1`. -/
noncomputable instance tracialMatrixQuotientSeminormedRing :
    SeminormedRing (TracialMatrixQuotient X l) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := by
    refine _root_.le_of_forall_pos_le_add fun ε hε ↦ ?_
    have hK : (0 : ℝ) < ‖x‖ + ‖y‖ + 1 := by positivity
    obtain ⟨δ, hδpos, hδ1, hδK⟩ :
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ * (‖x‖ + ‖y‖ + 1) ≤ ε := by
      refine ⟨min 1 (ε / (‖x‖ + ‖y‖ + 1)), lt_min one_pos (div_pos hε hK),
        min_le_left _ _, ?_⟩
      have hmin := mul_le_mul_of_nonneg_right
        (min_le_right (1 : ℝ) (ε / (‖x‖ + ‖y‖ + 1))) hK.le
      rwa [div_mul_cancel₀ _ hK.ne'] at hmin
    obtain ⟨a, ha_eq, ha⟩ := tracialQuot_exists_rep_norm_lt X l x hδpos
    obtain ⟨b, hb_eq, hb⟩ := tracialQuot_exists_rep_norm_lt X l y hδpos
    have hx0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
    have hy0 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
    have hab : ‖a‖ * ‖b‖ ≤ (‖x‖ + δ) * (‖y‖ + δ) :=
      mul_le_mul ha.le hb.le (norm_nonneg b) (by linarith)
    have hsq : δ * δ ≤ δ := by nlinarith
    calc ‖x * y‖
        = ‖Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) (a * b)‖ := by
          rw [map_mul, ha_eq, hb_eq]
      _ ≤ ‖a * b‖ := tracialQuot_norm_mk_le X l (a * b)
      _ ≤ ‖a‖ * ‖b‖ := norm_mul_le a b
      _ ≤ ‖x‖ * ‖y‖ + ε := by nlinarith

/-- Because the null ideal is closed, the quotient seminorm is a norm. -/
noncomputable instance tracialMatrixQuotientNormedRing :
    NormedRing (TracialMatrixQuotient X l) :=
  { tracialMatrixQuotientSeminormedRing X l,
    Submodule.Quotient.normedAddCommGroup (hilbertSchmidtNullIdeal X l) with }

/-- The tracial matrix quotient is complete. -/
noncomputable instance tracialMatrixQuotientCompleteSpace :
    CompleteSpace (TracialMatrixQuotient X l) :=
  Submodule.Quotient.completeSpace (hilbertSchmidtNullIdeal X l)

private def boundedSequenceStarHom :
    ModelBoundedSequence X →+ TracialMatrixQuotient X l :=
  (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l)).toAddMonoidHom.comp
    starAddEquiv.toAddMonoidHom

private theorem hilbertSchmidtNullIdeal_le_star_ker :
    (hilbertSchmidtNullIdeal X l).toAddSubgroup ≤
      (boundedSequenceStarHom X l).ker := by
  intro a ha
  change Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) (star a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hilbertSchmidtNullIdeal_star_mem X l ha

/-- Coordinatewise adjoint descends to the tracial quotient. -/
noncomputable instance tracialMatrixQuotientStar :
    Star (TracialMatrixQuotient X l) where
  star := QuotientAddGroup.lift
    (hilbertSchmidtNullIdeal X l).toAddSubgroup
    (boundedSequenceStarHom X l)
    (hilbertSchmidtNullIdeal_le_star_ker X l)

@[simp] theorem tracialMatrixQuotient_star_mk (a : ModelBoundedSequence X) :
    star (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) a) =
      Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) (star a) :=
  QuotientAddGroup.lift_mk _ _ _

noncomputable instance tracialMatrixQuotientInvolutiveStar :
    InvolutiveStar (TracialMatrixQuotient X l) where
  star_involutive x := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      change star (star (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) a)) =
        Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) a
      rw [tracialMatrixQuotient_star_mk, tracialMatrixQuotient_star_mk,
        star_star]

noncomputable instance tracialMatrixQuotientStarRing :
    StarRing (TracialMatrixQuotient X l) where
  star_add x y := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      induction y using QuotientAddGroup.induction_on with
      | _ b =>
        change star (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) (a + b)) =
          star (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) a) +
            star (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) b)
        rw [tracialMatrixQuotient_star_mk, tracialMatrixQuotient_star_mk,
          tracialMatrixQuotient_star_mk, star_add]
        rfl
  star_mul x y := by
    induction x using QuotientAddGroup.induction_on with
    | _ a =>
      induction y using QuotientAddGroup.induction_on with
      | _ b =>
        change star (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) (a * b)) =
          star (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) b) *
            star (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) a)
        rw [tracialMatrixQuotient_star_mk, tracialMatrixQuotient_star_mk,
          tracialMatrixQuotient_star_mk]
        rw [show star (a * b) = star b * star a from StarMul.star_mul a b]
        rfl

private theorem tracialMatrixQuotient_norm_star_le
    (x : TracialMatrixQuotient X l) : ‖star x‖ ≤ ‖x‖ := by
  apply _root_.le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, rfl, ha⟩ := tracialQuot_exists_rep_norm_lt X l x hε
  rw [tracialMatrixQuotient_star_mk]
  exact ((tracialQuot_norm_mk_le X l (star a)).trans_lt (by simpa using ha)).le

noncomputable instance tracialMatrixQuotientNormedStarGroup :
    NormedStarGroup (TracialMatrixQuotient X l) where
  norm_star_le := tracialMatrixQuotient_norm_star_le X l

/-- Audit pin: the descended adjoint is an isometry for the quotient norm. -/
theorem norm_tracialMatrixQuotient_star (x : TracialMatrixQuotient X l) :
    ‖star x‖ = ‖x‖ :=
  norm_star x

/-- The quotient's complex algebra structure is compatible with the quotient
norm. -/
noncomputable instance tracialMatrixQuotientNormedAlgebra :
    NormedAlgebra ℂ (TracialMatrixQuotient X l) :=
  ⟨fun z x ↦ (norm_smul z x).le⟩

/-- The descended adjoint is conjugate-linear. -/
noncomputable instance tracialMatrixQuotientStarModule :
    StarModule ℂ (TracialMatrixQuotient X l) := by
  constructor
  intro z x
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
      change star (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) (z • a)) =
        star z • star (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) a)
      rw [tracialMatrixQuotient_star_mk, tracialMatrixQuotient_star_mk,
        star_smul]
      rfl

/-- The quotient map onto the tracial quotient. -/
def tracialMatrixQuotientMk :
    ModelBoundedSequence X →+* TracialMatrixQuotient X l :=
  Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l)

@[simp] theorem tracialMatrixQuotientMk_apply (a : ModelBoundedSequence X) :
    tracialMatrixQuotientMk X l a =
      Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) a := rfl

theorem tracialMatrixQuotientMk_surjective :
    Function.Surjective (tracialMatrixQuotientMk X l) :=
  Ideal.Quotient.mk_surjective

/-- **A class vanishes exactly when a lift is `‖·‖₂`-null.**  This is the
statement faithfulness of the ultratrace is measured against. -/
theorem tracialMatrixQuotientMk_eq_zero_iff (a : ModelBoundedSequence X) :
    tracialMatrixQuotientMk X l a = 0 ↔ IsHilbertSchmidtNull X l a := by
  change Ideal.Quotient.mk (hilbertSchmidtNullIdeal X l) a = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  rfl

/-! ## The ultratrace on bounded sequences

`ulim` needs an ultrafilter, so the trace section is stated for `ω` rather
than for a general filter. -/

section Ultratrace

variable (ω : Ultrafilter ℕ)

omit [∀ n, Nonempty (X n)] in
/-- The coordinate normalized traces of a bounded sequence are bounded by its
uniform operator norm, hence converge along every ultrafilter. -/
theorem exists_tendsto_normTrace (a : ModelBoundedSequence X) :
    ∃ L : ℂ, Tendsto (fun n ↦ normTrace (X n) (a n)) (ω : Filter ℕ) (nhds L) :=
  UltrafilterLimit.exists_tendsto_of_bounded ω (C := ‖a‖) fun n ↦
    (PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm (X n) (a n)).trans
      (boundedMatrixSequence_coord_norm_le (fun n ↦ X n) a n)

/-- **`lim_ω tr_{X n}(a n)`**, the ultratrace of a bounded matrix sequence. -/
def seqUltratrace (a : ModelBoundedSequence X) : ℂ :=
  UltrafilterLimit.ulim ω (fun n ↦ normTrace (X n) (a n))

omit [∀ n, Nonempty (X n)] in
theorem tendsto_seqUltratrace (a : ModelBoundedSequence X) :
    Tendsto (fun n ↦ normTrace (X n) (a n)) (ω : Filter ℕ)
      (nhds (seqUltratrace X ω a)) :=
  UltrafilterLimit.tendsto_ulim (exists_tendsto_normTrace X ω a)

omit [∀ n, Nonempty (X n)] in
theorem seqUltratrace_zero :
    seqUltratrace X ω (0 : ModelBoundedSequence X) = 0 := by
  refine UltrafilterLimit.ulim_eq ?_
  refine tendsto_const_nhds.congr fun n ↦ ?_
  exact (normTrace_zero (X n)).symm

omit [∀ n, Nonempty (X n)] in
theorem seqUltratrace_add (a b : ModelBoundedSequence X) :
    seqUltratrace X ω (a + b) = seqUltratrace X ω a + seqUltratrace X ω b := by
  refine UltrafilterLimit.ulim_eq ?_
  refine ((tendsto_seqUltratrace X ω a).add (tendsto_seqUltratrace X ω b)).congr
    fun n ↦ ?_
  exact (normTrace_add (X n) (a n) (b n)).symm

theorem seqUltratrace_smul (c : ℂ) (a : ModelBoundedSequence X) :
    seqUltratrace X ω (c • a) = c * seqUltratrace X ω a := by
  refine UltrafilterLimit.ulim_eq ?_
  refine (tendsto_const_nhds.mul (tendsto_seqUltratrace X ω a)).congr fun n ↦ ?_
  exact (normTrace_smul (X n) c (a n)).symm

theorem seqUltratrace_one :
    seqUltratrace X ω (1 : ModelBoundedSequence X) = 1 := by
  refine UltrafilterLimit.ulim_eq ?_
  refine tendsto_const_nhds.congr fun n ↦ ?_
  exact (normTrace_one' (X n) Fintype.card_pos).symm

omit [∀ n, Nonempty (X n)] in
theorem seqUltratrace_mul_comm (a b : ModelBoundedSequence X) :
    seqUltratrace X ω (a * b) = seqUltratrace X ω (b * a) := by
  refine UltrafilterLimit.ulim_eq ?_
  refine (tendsto_seqUltratrace X ω (b * a)).congr fun n ↦ ?_
  exact normTrace_mul_comm (X n) (b n) (a n)

omit [∀ n, Nonempty (X n)] in
theorem seqUltratrace_star (a : ModelBoundedSequence X) :
    seqUltratrace X ω (star a) = star (seqUltratrace X ω a) := by
  refine UltrafilterLimit.ulim_eq ?_
  have hc : Tendsto (fun n ↦ star (normTrace (X n) (a n))) (ω : Filter ℕ)
      (nhds (star (seqUltratrace X ω a))) :=
    (continuous_star.tendsto _).comp (tendsto_seqUltratrace X ω a)
  refine hc.congr fun n ↦ ?_
  have h : (star a) n = (a n)ᴴ := Matrix.star_eq_conjTranspose (a n)
  rw [h, normTrace_conjTranspose]
  rfl

omit [∀ n, Nonempty (X n)] in
/-- `|lim_ω tr_{X n}(a n)| ≤ ‖a‖`: the second printed inequality
`|tr_r(x)| ≤ ‖x‖` survives the ultralimit. -/
theorem norm_seqUltratrace_le (a : ModelBoundedSequence X) :
    ‖seqUltratrace X ω a‖ ≤ ‖a‖ := by
  have hn : Tendsto (fun n ↦ ‖normTrace (X n) (a n)‖) (ω : Filter ℕ)
      (nhds ‖seqUltratrace X ω a‖) :=
    (continuous_norm.tendsto _).comp (tendsto_seqUltratrace X ω a)
  refine le_of_tendsto' hn fun n ↦ ?_
  exact (PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm (X n) (a n)).trans
    (boundedMatrixSequence_coord_norm_le (fun n ↦ X n) a n)

omit [∀ n, Nonempty (X n)] in
/-- **Well-definedness on the quotient.**  Two lifts differing by a
`‖·‖₂`-null sequence have the same ultratrace, because `|tr_r(x)| ≤ ‖x‖₂`. -/
theorem seqUltratrace_eq_of_sub_isHilbertSchmidtNull
    {a b : ModelBoundedSequence X}
    (h : IsHilbertSchmidtNull X (ω : Filter ℕ) (a - b)) :
    seqUltratrace X ω a = seqUltratrace X ω b := by
  have h' : Tendsto (fun n ↦ hsNorm (X n) ((a - b) n)) (ω : Filter ℕ)
      (nhds 0) := h
  have hzero : Tendsto (fun n ↦ normTrace (X n) (a n) - normTrace (X n) (b n))
      (ω : Filter ℕ) (nhds 0) := by
    refine squeeze_zero_norm (fun n ↦ ?_) h'
    rw [← normTrace_sub (X n) (a n) (b n)]
    exact norm_normTrace_le_hsNorm (X n) ((a - b) n)
  have hdiff := (tendsto_seqUltratrace X ω a).sub (tendsto_seqUltratrace X ω b)
  have huniq := tendsto_nhds_unique hdiff hzero
  linear_combination huniq

/-! ### The squared Hilbert--Schmidt ultralimit

`trω (x* x)` is real and nonnegative because it *is* the ultralimit of the
squared normalized Hilbert--Schmidt norms of any lift. -/

omit [∀ n, Nonempty (X n)] in
theorem exists_tendsto_hsNormSq (a : ModelBoundedSequence X) :
    ∃ L : ℝ, Tendsto (fun n ↦ hsNormSq (X n) (a n)) (ω : Filter ℕ) (nhds L) :=
  UltrafilterLimit.exists_tendsto_of_bounded ω (C := ‖a‖ ^ 2) fun n ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hsNormSq_nonneg (X n) (a n))]
    exact hsNormSq_coord_le X a n

/-- `lim_ω ‖a n‖₂²`. -/
def seqHSLimit (a : ModelBoundedSequence X) : ℝ :=
  UltrafilterLimit.ulim ω (fun n ↦ hsNormSq (X n) (a n))

omit [∀ n, Nonempty (X n)] in
theorem tendsto_seqHSLimit (a : ModelBoundedSequence X) :
    Tendsto (fun n ↦ hsNormSq (X n) (a n)) (ω : Filter ℕ)
      (nhds (seqHSLimit X ω a)) :=
  UltrafilterLimit.tendsto_ulim (exists_tendsto_hsNormSq X ω a)

omit [∀ n, Nonempty (X n)] in
theorem seqHSLimit_nonneg (a : ModelBoundedSequence X) :
    0 ≤ seqHSLimit X ω a :=
  UltrafilterLimit.ulim_nonneg (exists_tendsto_hsNormSq X ω a)
    fun n ↦ hsNormSq_nonneg (X n) (a n)

omit [∀ n, Nonempty (X n)] in
/-- **The vanishing criterion.**  The squared Hilbert--Schmidt ultralimit
vanishes exactly on the ideal that is divided out. -/
theorem seqHSLimit_eq_zero_iff (a : ModelBoundedSequence X) :
    seqHSLimit X ω a = 0 ↔ IsHilbertSchmidtNull X (ω : Filter ℕ) a := by
  rw [isHilbertSchmidtNull_iff_sq]
  constructor
  · intro h
    have ht := tendsto_seqHSLimit X ω a
    rwa [h] at ht
  · intro h
    exact UltrafilterLimit.ulim_eq h

omit [∀ n, Nonempty (X n)] in
/-- **`trω (a* a) = lim_ω ‖a n‖₂²`.**  This single identity supplies
positivity and faithfulness at once. -/
theorem seqUltratrace_star_mul_self (a : ModelBoundedSequence X) :
    seqUltratrace X ω (star a * a) = ((seqHSLimit X ω a : ℝ) : ℂ) := by
  refine UltrafilterLimit.ulim_eq ?_
  have hC : Tendsto (fun n ↦ ((hsNormSq (X n) (a n) : ℝ) : ℂ)) (ω : Filter ℕ)
      (nhds ((seqHSLimit X ω a : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (tendsto_seqHSLimit X ω a)
  refine hC.congr fun n ↦ ?_
  have hstar : (star a * a) n = (a n)ᴴ * (a n) := by
    show star (a n) * (a n) = (a n)ᴴ * (a n)
    rw [Matrix.star_eq_conjTranspose]
  rw [hstar]
  exact ofReal_hsNormSq_conjTranspose_mul (X n) (a n)

end Ultratrace

/-! ## The ultratrace on the quotient -/

section QuotientTrace

variable (ω : Ultrafilter ℕ)

private def seqUltratraceHom : ModelBoundedSequence X →+ ℂ where
  toFun := seqUltratrace X ω
  map_zero' := seqUltratrace_zero X ω
  map_add' := seqUltratrace_add X ω

private theorem hilbertSchmidtNullIdeal_le_ultratrace_ker :
    (hilbertSchmidtNullIdeal X (ω : Filter ℕ)).toAddSubgroup ≤
      (seqUltratraceHom X ω).ker := by
  intro a ha
  change seqUltratrace X ω a = 0
  have hsub : IsHilbertSchmidtNull X (ω : Filter ℕ) (a - 0) := by
    rw [sub_zero]
    exact ha
  rw [seqUltratrace_eq_of_sub_isHilbertSchmidtNull X ω hsub]
  exact seqUltratrace_zero X ω

/-- **The ultratrace `trω` on `Mω`.**  It sends the class of `a` to
`lim_ω tr_{X n}(a n)`. -/
def ultratrace : TracialMatrixQuotient X (ω : Filter ℕ) →+ ℂ :=
  QuotientAddGroup.lift (hilbertSchmidtNullIdeal X (ω : Filter ℕ)).toAddSubgroup
    (seqUltratraceHom X ω) (hilbertSchmidtNullIdeal_le_ultratrace_ker X ω)

@[simp] theorem ultratrace_mk (a : ModelBoundedSequence X) :
    ultratrace X ω (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X (ω : Filter ℕ)) a)
      = seqUltratrace X ω a :=
  QuotientAddGroup.lift_mk _ _ _

theorem ultratrace_add (x y : TracialMatrixQuotient X (ω : Filter ℕ)) :
    ultratrace X ω (x + y) = ultratrace X ω x + ultratrace X ω y :=
  map_add (ultratrace X ω) x y

/-- The ultratrace is complex homogeneous. -/
theorem ultratrace_smul (c : ℂ) (x : TracialMatrixQuotient X (ω : Filter ℕ)) :
    ultratrace X ω (c • x) = c * ultratrace X ω x := by
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
    change ultratrace X ω
        (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X (ω : Filter ℕ)) (c • a))
      = c * ultratrace X ω
        (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X (ω : Filter ℕ)) a)
    rw [ultratrace_mk, ultratrace_mk]
    exact seqUltratrace_smul X ω c a

/-- The ultratrace as a complex-linear functional. -/
def ultratraceLinearMap :
    TracialMatrixQuotient X (ω : Filter ℕ) →ₗ[ℂ] ℂ where
  toFun := ultratrace X ω
  map_add' := ultratrace_add X ω
  map_smul' c x := by
    change ultratrace X ω (c • x) = c * ultratrace X ω x
    exact ultratrace_smul X ω c x

@[simp] theorem ultratraceLinearMap_apply
    (x : TracialMatrixQuotient X (ω : Filter ℕ)) :
    ultratraceLinearMap X ω x = ultratrace X ω x := rfl

/-- **Traciality.** -/
theorem ultratrace_mul_comm (x y : TracialMatrixQuotient X (ω : Filter ℕ)) :
    ultratrace X ω (x * y) = ultratrace X ω (y * x) := by
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
    induction y using QuotientAddGroup.induction_on with
    | _ b =>
      change ultratrace X ω
          (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X (ω : Filter ℕ)) (a * b))
        = ultratrace X ω
          (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X (ω : Filter ℕ)) (b * a))
      rw [ultratrace_mk, ultratrace_mk]
      exact seqUltratrace_mul_comm X ω a b

/-- **`*`-compatibility**: `trω (x*) = conj (trω x)`. -/
theorem ultratrace_star (x : TracialMatrixQuotient X (ω : Filter ℕ)) :
    ultratrace X ω (star x) = star (ultratrace X ω x) := by
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
    change ultratrace X ω
        (star (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X (ω : Filter ℕ)) a))
      = star (ultratrace X ω
        (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X (ω : Filter ℕ)) a))
    rw [tracialMatrixQuotient_star_mk, ultratrace_mk, ultratrace_mk]
    exact seqUltratrace_star X ω a

/-- **Contractivity**: `|trω x| ≤ ‖x‖` for the quotient norm.  Together with
`ultratrace_one` and `ultratrace_star_mul_self_nonneg` this makes `trω` a
tracial state on `Mω`, not merely a linear functional. -/
theorem norm_ultratrace_le (x : TracialMatrixQuotient X (ω : Filter ℕ)) :
    ‖ultratrace X ω x‖ ≤ ‖x‖ := by
  refine _root_.le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨a, ha_eq, ha⟩ :=
    tracialQuot_exists_rep_norm_lt X (ω : Filter ℕ) x hε
  have h1 : ultratrace X ω x = seqUltratrace X ω a := by
    rw [← ha_eq, ultratrace_mk]
  rw [h1]
  exact (norm_seqUltratrace_le X ω a).trans ha.le

/-- **Normalization**: `trω 1 = 1`.  The positive dimensionality that makes
this true is carried by the `Nonempty` instance on the models. -/
theorem ultratrace_one :
    ultratrace X ω (1 : TracialMatrixQuotient X (ω : Filter ℕ)) = 1 := by
  have h1 : (1 : TracialMatrixQuotient X (ω : Filter ℕ))
      = Ideal.Quotient.mk (hilbertSchmidtNullIdeal X (ω : Filter ℕ)) 1 :=
    (map_one (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X (ω : Filter ℕ)))).symm
  rw [h1, ultratrace_mk]
  exact seqUltratrace_one X ω

/-- **`trω (x* x)` is the ultralimit of the squared Hilbert--Schmidt norms of
any lift.**  Everything about positivity and faithfulness reduces to this. -/
theorem ultratrace_star_mul_self_eq_ofReal (a : ModelBoundedSequence X) :
    ultratrace X ω
        (star (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X (ω : Filter ℕ)) a) *
          Ideal.Quotient.mk (hilbertSchmidtNullIdeal X (ω : Filter ℕ)) a)
      = ((seqHSLimit X ω a : ℝ) : ℂ) := by
  rw [tracialMatrixQuotient_star_mk]
  change ultratrace X ω
      (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X (ω : Filter ℕ)) (star a * a))
    = ((seqHSLimit X ω a : ℝ) : ℂ)
  rw [ultratrace_mk]
  exact seqUltratrace_star_mul_self X ω a

/-- **Positivity**: `trω (x* x)` is a nonnegative real. -/
theorem ultratrace_star_mul_self_nonneg
    (x : TracialMatrixQuotient X (ω : Filter ℕ)) :
    ∃ t : ℝ, 0 ≤ t ∧ ultratrace X ω (star x * x) = (t : ℂ) := by
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
    refine ⟨seqHSLimit X ω a, seqHSLimit_nonneg X ω a, ?_⟩
    exact ultratrace_star_mul_self_eq_ofReal X ω a

/-- **Faithfulness**: `trω (x* x) = 0` forces `x = 0`.  The identity
`‖A‖₂² = tr_r(Aᴴ A)` makes this the statement that the squared
Hilbert--Schmidt ultralimit of a lift vanishes exactly on the ideal that was
divided out. -/
theorem ultratrace_star_mul_self_eq_zero_iff
    (x : TracialMatrixQuotient X (ω : Filter ℕ)) :
    ultratrace X ω (star x * x) = 0 ↔ x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | _ a =>
    have hmk : ultratrace X ω
          (star (Ideal.Quotient.mk (hilbertSchmidtNullIdeal X (ω : Filter ℕ)) a) *
            Ideal.Quotient.mk (hilbertSchmidtNullIdeal X (ω : Filter ℕ)) a) = 0
        ↔ Ideal.Quotient.mk (hilbertSchmidtNullIdeal X (ω : Filter ℕ)) a = 0 := by
      rw [ultratrace_star_mul_self_eq_ofReal X ω a, Complex.ofReal_eq_zero,
        seqHSLimit_eq_zero_iff X ω a, Ideal.Quotient.eq_zero_iff_mem]
      exact Iff.rfl
    exact hmk

end QuotientTrace

end

end TracialUltraproduct
end GroupApproximation
