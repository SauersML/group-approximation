import GroupApproximation.Analysis.UniformTracialGNSTwoGauge
import GroupApproximation.Analysis.TracialStateWeakStarTopology

/-!
# Tracially complete C-star algebras, factoriality, and the trace problem

STW Problem XXII is a question about **factorial tracially complete C-star
algebras**.  This file supplies the two words, so that a purported
counterexample can be made to say what the problem asks.

The definitions are those of Carrion--Castillejos--Evington--Gabe--Schafhauser
--Tikuisis--White, *Tracially complete C\*-algebras*, arXiv:2310.20594.
Verbatim, in that paper's notation:

* Definition 3.4.  "A tracially complete C\*-algebra is a pair `(M, X)` where
  `M` is a C\*-algebra and `X ⊆ T(M)` is a compact convex set such that
  (i) `X` is a faithful set of traces on `M`, and (ii) the unit ball of `M` is
  `‖·‖_{2,X}`-complete."
* Definition 3.13.  "A tracially complete C\*-algebra `(M, X)` is said to be
  *factorial* if `X` is a closed face of `T(M)`."
* Question 1.1 (the trace problem).  "Let `(M, X)` be a factorial tracially
  complete C\*-algebra.  Are all traces on `M` automatically
  `‖·‖_{2,X}`-continuous?  Equivalently, is the inclusion `X ⊆ T(M)` an
  equality?"

The uniform two-norm is `‖a‖_{2,X} = sup_{τ ∈ X} τ (a⋆ a)^{1/2}`, which in this
project's vocabulary is the supremum over `X` of `tracialTwoNorm`.

Everything here is stated for the project's bundled `TracialState`, whose weak-
star (pointwise) topology is the one installed in
`Analysis/TracialStateWeakStarTopology`.  `T(M)` is the whole type
`TracialState M`, so "`X ⊆ T(M)` is an equality" is literally `X = Set.univ`.

## Contents

* convex combinations of tracial states, and hence convex subsets and faces of
  the trace simplex;
* `uniformTwoNormOn`, `IsFaithfulTraceSet`, `IsUniformTwoContinuousOn`,
  `UnitBallUniformTwoComplete`;
* `IsTraciallyCompletePair` and `IsFactorialTraciallyCompletePair`;
* weak-star compactness of the whole trace space of a unital C-star algebra
  (Banach--Alaoglu through Tychonoff), which is what makes `IsCompact X`
  reachable from `IsClosed X`;
* `dominatedByGauge`: the tracial states whose two-norm is bounded by a fixed
  gauge.  Such a set is always convex and weak-star closed, and it is a face as
  soon as it is stable under the two-norm rescaling produced by domination.
  This is the route by which a uniform tracial completion is factorial.
-/

namespace GroupApproximation
namespace TraciallyComplete

open Filter
open UniformTracialGNSTwoGauge
open scoped ComplexOrder

noncomputable section

universe u

/-! ## Convex combinations of tracial states -/

section ConvexComb

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]

/-- Multiplying a nonnegative complex number by a nonnegative real scalar keeps
it nonnegative.  Spelled out rather than taken from the scoped ordered-ring
instance on `ℂ`, so that this file does not depend on it. -/
theorem ofReal_mul_nonneg {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 0 ≤ z) :
    0 ≤ (t : ℂ) * z := by
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hz
  refine Complex.nonneg_iff.mpr ⟨?_, ?_⟩
  · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg ht hre
  · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      ← him, mul_zero]

/-- Bundled tracial states are determined by their values. -/
theorem tracialState_ext {σ τ : TracialState A} (h : ∀ a, σ a = τ a) : σ = τ := by
  cases σ with
  | mk f hf1 hfp hft =>
    cases τ with
    | mk g hg1 hgp hgt =>
      have hfg : f = g := LinearMap.ext h
      subst g
      rfl

/-- The functional underlying the convex combination `t σ + (1 - t) τ`. -/
def convexCombLinearMap (t : ℝ) (σ τ : TracialState A) : A →ₗ[ℂ] ℂ :=
  (t : ℂ) • σ.toLinearMap + ((1 - t : ℝ) : ℂ) • τ.toLinearMap

@[simp] theorem convexCombLinearMap_apply (t : ℝ) (σ τ : TracialState A) (a : A) :
    convexCombLinearMap t σ τ a = (t : ℂ) * σ a + ((1 - t : ℝ) : ℂ) * τ a := by
  change (t : ℂ) • σ.toLinearMap a + ((1 - t : ℝ) : ℂ) • τ.toLinearMap a
      = (t : ℂ) * σ a + ((1 - t : ℝ) : ℂ) * τ a
  simp only [smul_eq_mul]

/-- The convex combination `t σ + (1 - t) τ` of two tracial states.  This is the
convex structure of the trace simplex `T(A)`; there is no ambient vector space
here, so the operation is given directly. -/
def convexComb (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (σ τ : TracialState A) :
    TracialState A where
  toLinearMap := convexCombLinearMap t σ τ
  map_one := by
    have h : convexCombLinearMap t σ τ (1 : A)
        = (t : ℂ) * σ 1 + ((1 - t : ℝ) : ℂ) * τ 1 :=
      convexCombLinearMap_apply t σ τ 1
    rw [h, TracialState.apply_one, TracialState.apply_one, mul_one, mul_one]
    push_cast
    ring
  map_star_mul_self_nonneg x := by
    have h : convexCombLinearMap t σ τ (star x * x)
        = (t : ℂ) * σ (star x * x) + ((1 - t : ℝ) : ℂ) * τ (star x * x) :=
      convexCombLinearMap_apply t σ τ _
    rw [h]
    have h1 : (0 : ℝ) ≤ 1 - t := by linarith
    exact add_nonneg (ofReal_mul_nonneg ht0 (σ.map_star_mul_self_nonneg x))
      (ofReal_mul_nonneg h1 (τ.map_star_mul_self_nonneg x))
  map_mul_comm x y := by
    have hxy : convexCombLinearMap t σ τ (x * y)
        = (t : ℂ) * σ (x * y) + ((1 - t : ℝ) : ℂ) * τ (x * y) :=
      convexCombLinearMap_apply t σ τ _
    have hyx : convexCombLinearMap t σ τ (y * x)
        = (t : ℂ) * σ (y * x) + ((1 - t : ℝ) : ℂ) * τ (y * x) :=
      convexCombLinearMap_apply t σ τ _
    rw [hxy, hyx, σ.map_mul_comm x y, τ.map_mul_comm x y]

@[simp] theorem convexComb_apply (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (σ τ : TracialState A) (a : A) :
    convexComb t ht0 ht1 σ τ a = (t : ℂ) * σ a + ((1 - t : ℝ) : ℂ) * τ a :=
  convexCombLinearMap_apply t σ τ a

/-- The real part of a convex combination is the convex combination of the real
parts. -/
theorem convexComb_re (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (σ τ : TracialState A) (a : A) :
    (convexComb t ht0 ht1 σ τ a).re = t * (σ a).re + (1 - t) * (τ a).re := by
  rw [convexComb_apply, Complex.add_re, Complex.mul_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, zero_mul, sub_zero, sub_zero]

end ConvexComb

/-! ## The uniform two-norm of a set of traces -/

section UniformTwoNorm

variable {A : Type u} [CStarAlgebra A]

/-- **The uniform two-norm** `‖a‖_{2,X} = sup_{τ ∈ X} τ (a⋆ a)^{1/2}` of
CCEGSTW §3.1. -/
def uniformTwoNormOn (X : Set (TracialState A)) (a : A) : ℝ :=
  sSup ((fun τ : TracialState A ↦ tracialTwoNorm τ a) '' X)

theorem bddAbove_image_tracialTwoNorm (X : Set (TracialState A)) (a : A) :
    BddAbove ((fun τ : TracialState A ↦ tracialTwoNorm τ a) '' X) := by
  refine ⟨‖a‖, ?_⟩
  rintro _ ⟨τ, -, rfl⟩
  exact tracialTwoNorm_le_norm τ a

theorem tracialTwoNorm_le_uniformTwoNormOn {X : Set (TracialState A)}
    {τ : TracialState A} (hτ : τ ∈ X) (a : A) :
    tracialTwoNorm τ a ≤ uniformTwoNormOn X a :=
  le_csSup (bddAbove_image_tracialTwoNorm X a) ⟨τ, hτ, rfl⟩

theorem uniformTwoNormOn_le {X : Set (TracialState A)} (hX : X.Nonempty)
    {a : A} {c : ℝ} (h : ∀ τ ∈ X, tracialTwoNorm τ a ≤ c) :
    uniformTwoNormOn X a ≤ c := by
  refine csSup_le (hX.image _) ?_
  rintro _ ⟨τ, hτ, rfl⟩
  exact h τ hτ

theorem uniformTwoNormOn_nonneg {X : Set (TracialState A)} (hX : X.Nonempty)
    (a : A) : 0 ≤ uniformTwoNormOn X a := by
  obtain ⟨τ, hτ⟩ := hX
  exact (tracialTwoNorm_nonneg τ a).trans
    (tracialTwoNorm_le_uniformTwoNormOn hτ a)

/-- A tracial state is bounded by its own trace two-norm; the Cauchy--Schwarz
estimate against the class of `1`. -/
theorem norm_apply_le_tracialTwoNorm (σ : TracialState A) (a : A) :
    ‖σ a‖ ≤ tracialTwoNorm σ a := by
  have h := norm_apply_star_mul_le σ (1 : A) a
  rwa [star_one, one_mul, tracialTwoNorm_one, one_mul] at h

end UniformTwoNorm

/-! ## Faithfulness, two-continuity, and completeness of the unit ball -/

section Axioms

variable {A : Type u} [CStarAlgebra A]

/-- CCEGSTW Definition 3.4(i): `X` is a **faithful** set of traces on `A`. -/
def IsFaithfulTraceSet (X : Set (TracialState A)) : Prop :=
  ∀ a : A, (∀ τ ∈ X, τ (star a * a) = 0) → a = 0

/-- A tracial state is `‖·‖_{2,X}`-continuous.  Sequential continuity at zero,
which is the form used throughout this project's XXII development; for a linear
functional it is equivalent to continuity. -/
def IsUniformTwoContinuousOn (X : Set (TracialState A))
    (σ : TracialState A) : Prop :=
  ∀ x : ℕ → A,
    Tendsto (fun k ↦ uniformTwoNormOn X (x k)) atTop (nhds 0) →
    Tendsto (fun k ↦ σ (x k)) atTop (nhds 0)

/-- A tracial state dominated by the uniform two-norm is two-continuous. -/
theorem isUniformTwoContinuousOn_of_norm_le {X : Set (TracialState A)}
    {σ : TracialState A} {C : ℝ}
    (h : ∀ a : A, ‖σ a‖ ≤ C * uniformTwoNormOn X a) :
    IsUniformTwoContinuousOn X σ := by
  intro x hx
  refine squeeze_zero_norm (fun k ↦ h (x k)) ?_
  simpa using hx.const_mul C

/-- CCEGSTW Definition 3.4(ii): the unit ball of `A` is `‖·‖_{2,X}`-complete. -/
def UnitBallUniformTwoComplete (X : Set (TracialState A)) : Prop :=
  ∀ x : ℕ → A, (∀ k, ‖x k‖ ≤ 1) →
    (∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ l ≥ K,
      uniformTwoNormOn X (x k - x l) < ε) →
    ∃ a : A, ‖a‖ ≤ 1 ∧
      Tendsto (fun k ↦ uniformTwoNormOn X (x k - a)) atTop (nhds 0)

end Axioms

/-! ## Convex subsets and faces of the trace simplex -/

section Faces

variable {A : Type u} [Ring A] [StarRing A] [Algebra ℂ A]

/-- `X` is a convex subset of the trace simplex `T(A)`. -/
def IsConvexTraceSet (X : Set (TracialState A)) : Prop :=
  ∀ σ ∈ X, ∀ τ ∈ X, ∀ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
    convexComb t ht0 ht1 σ τ ∈ X

/-- `X` is a **face** of the trace simplex `T(A)`: a convex subset such that
whenever a proper convex combination of two tracial states lies in `X`, both of
them already do.  This is the notion in CCEGSTW Definition 3.13. -/
structure IsFaceTraceSet (X : Set (TracialState A)) : Prop where
  isConvex : IsConvexTraceSet X
  mem_of_convexComb_mem : ∀ (σ τ : TracialState A) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1),
    convexComb t ht0.le ht1.le σ τ ∈ X → σ ∈ X ∧ τ ∈ X

end Faces

/-! ## Tracially complete and factorial tracially complete pairs -/

section Pairs

variable {A : Type u} [CStarAlgebra A]

/-- **CCEGSTW Definition 3.4.**  `(A, X)` is a tracially complete C-star
algebra: `X` is a compact convex set of tracial states which is faithful, and
the unit ball of `A` is `‖·‖_{2,X}`-complete.

The paper's degenerate empty case is excluded: `nonempty` is the paper's
"implicitly we always imagine `X` to be non-empty". -/
structure IsTraciallyCompletePair (X : Set (TracialState A)) : Prop where
  nonempty : X.Nonempty
  isCompact : IsCompact X
  isConvex : IsConvexTraceSet X
  faithful : IsFaithfulTraceSet X
  unitBallComplete : UnitBallUniformTwoComplete X

/-- **CCEGSTW Definition 3.13.**  A tracially complete C-star algebra `(A, X)`
is *factorial* if `X` is a closed face of `T(A)`. -/
structure IsFactorialTraciallyCompletePair (X : Set (TracialState A)) : Prop where
  toIsTraciallyCompletePair : IsTraciallyCompletePair X
  isClosed : IsClosed X
  isFace : IsFaceTraceSet X

/-- **The trace problem, CCEGSTW Question 1.1, first form.**  Every tracial
state of `A` is `‖·‖_{2,X}`-continuous. -/
def AllTracesUniformTwoContinuous (X : Set (TracialState A)) : Prop :=
  ∀ σ : TracialState A, IsUniformTwoContinuousOn X σ

/-- **The trace problem, CCEGSTW Question 1.1, second form.**  The inclusion
`X ⊆ T(A)` is an equality.  `T(A)` is the whole type here. -/
def DesignatedTracesAreAllTraces (X : Set (TracialState A)) : Prop :=
  X = Set.univ

/-- When `X` is exactly the set of `‖·‖_{2,X}`-continuous tracial states -- the
situation of CCEGSTW Proposition 3.15 for a factorial pair -- the two forms of
the trace problem agree. -/
theorem allTracesUniformTwoContinuous_iff_designatedTracesAreAllTraces
    {X : Set (TracialState A)}
    (hX : ∀ σ : TracialState A, σ ∈ X ↔ IsUniformTwoContinuousOn X σ) :
    AllTracesUniformTwoContinuous X ↔ DesignatedTracesAreAllTraces X := by
  constructor
  · intro h
    exact Set.eq_univ_of_forall fun σ ↦ (hX σ).2 (h σ)
  · intro h σ
    exact (hX σ).1 (by rw [h]; exact Set.mem_univ σ)

end Pairs

/-! ## Weak-star compactness of the trace space

CCEGSTW Definition 3.4 asks `X` to be compact.  For a norm-closed set of traces
that is Banach--Alaoglu; here it is obtained directly, by realising
`TracialState A` as a closed subset of a product of closed discs. -/

section Compactness

variable (A : Type u) [CStarAlgebra A]

/-- The product of closed discs of radius `‖a‖`, one for each `a : A`. -/
def traceBox : Set (A → ℂ) :=
  Set.univ.pi fun a : A ↦ Metric.closedBall (0 : ℂ) ‖a‖

theorem isCompact_traceBox : IsCompact (traceBox A) :=
  isCompact_univ_pi fun a ↦ isCompact_closedBall (0 : ℂ) ‖a‖

/-- The algebraic conditions cutting the tracial states out of the box. -/
def traceLocus : Set (A → ℂ) :=
  {f | (∀ x y : A, f (x + y) = f x + f y) ∧
    (∀ (c : ℂ) (x : A), f (c • x) = c * f x) ∧
    f 1 = 1 ∧
    (∀ x : A, 0 ≤ f (star x * x)) ∧
    (∀ x y : A, f (x * y) = f (y * x))}

/-- The nonnegative complex numbers form a closed set. -/
theorem isClosed_complexNonneg : IsClosed {z : ℂ | 0 ≤ z} := by
  have hset : {z : ℂ | 0 ≤ z} = {z : ℂ | 0 ≤ z.re} ∩ {z : ℂ | 0 = z.im} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    exact Complex.nonneg_iff
  rw [hset]
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_eq continuous_const Complex.continuous_im)

theorem isClosed_traceLocus : IsClosed (traceLocus A) := by
  have h1 : IsClosed {f : A → ℂ | ∀ x y : A, f (x + y) = f x + f y} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ ?_
    exact isClosed_eq (continuous_apply (x + y))
      ((continuous_apply x).add (continuous_apply y))
  have h2 : IsClosed {f : A → ℂ | ∀ (c : ℂ) (x : A), f (c • x) = c * f x} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun c ↦ isClosed_iInter fun x ↦ ?_
    exact isClosed_eq (continuous_apply (c • x))
      (continuous_const.mul (continuous_apply x))
  have h3 : IsClosed {f : A → ℂ | f 1 = 1} :=
    isClosed_eq (continuous_apply (1 : A)) continuous_const
  have h4 : IsClosed {f : A → ℂ | ∀ x : A, 0 ≤ f (star x * x)} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun x ↦ ?_
    have hpre : {f : A → ℂ | 0 ≤ f (star x * x)}
        = (fun g : A → ℂ ↦ g (star x * x)) ⁻¹' {z : ℂ | 0 ≤ z} := rfl
    rw [hpre]
    exact isClosed_complexNonneg.preimage (continuous_apply (star x * x))
  have h5 : IsClosed {f : A → ℂ | ∀ x y : A, f (x * y) = f (y * x)} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ ?_
    exact isClosed_eq (continuous_apply (x * y)) (continuous_apply (y * x))
  have hEq : traceLocus A =
      {f : A → ℂ | ∀ x y : A, f (x + y) = f x + f y} ∩
        ({f : A → ℂ | ∀ (c : ℂ) (x : A), f (c • x) = c * f x} ∩
          ({f : A → ℂ | f 1 = 1} ∩
            ({f : A → ℂ | ∀ x : A, 0 ≤ f (star x * x)} ∩
              {f : A → ℂ | ∀ x y : A, f (x * y) = f (y * x)}))) := rfl
  rw [hEq]
  exact h1.inter (h2.inter (h3.inter (h4.inter h5)))

theorem range_tracialStateEvaluation :
    Set.range (tracialStateEvaluation (A := A)) = traceBox A ∩ traceLocus A := by
  ext f
  constructor
  · rintro ⟨τ, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine Set.mem_univ_pi.2 fun a ↦ ?_
      refine mem_closedBall_zero_iff.2 ?_
      exact Manuscript.MFRecognition.TensorSynchronization.norm_tracialState_le τ a
    · intro x y
      exact τ.map_add x y
    · intro c x
      have h := τ.map_smul c x
      rwa [smul_eq_mul] at h
    · exact τ.map_one
    · intro x
      exact τ.map_star_mul_self_nonneg x
    · intro x y
      exact τ.map_mul_comm x y
  · rintro ⟨-, hadd, hsmul, hone, hpos, hcomm⟩
    refine ⟨⟨{ toFun := f
               map_add' := hadd
               map_smul' := ?_ }, hone, hpos, hcomm⟩, rfl⟩
    intro c x
    simpa using hsmul c x

/-- **The trace space of a unital C-star algebra is weak-star compact.** -/
theorem compactSpace_tracialState : CompactSpace (TracialState A) := by
  rw [← isCompact_univ_iff]
  rw [isEmbedding_tracialStateEvaluation.isInducing.isCompact_iff, Set.image_univ,
    range_tracialStateEvaluation]
  exact (isCompact_traceBox A).inter_right (isClosed_traceLocus A)

variable {A}

/-- A weak-star closed set of tracial states is weak-star compact. -/
theorem isCompact_of_isClosed_tracialState {X : Set (TracialState A)}
    (hX : IsClosed X) : IsCompact X := by
  haveI := compactSpace_tracialState A
  exact hX.isCompact

end Compactness

/-! ## Trace sets cut out by a gauge

A uniform tracial completion carries a distinguished gauge -- the uniform
two-norm of the algebra it completes -- and its designated traces are exactly
the tracial states dominated by that gauge.  Such a set is automatically convex
and weak-star closed.  Its being a *face* is the extra input, and it needs one
hypothesis: that the rescaling produced by domination does not leave the set. -/

section Gauge

variable {A : Type u} [CStarAlgebra A]

/-- The tracial states whose trace two-norm is dominated by a gauge `N`. -/
def dominatedByGauge (N : A → ℝ) : Set (TracialState A) :=
  {σ : TracialState A | ∀ a : A, tracialTwoNorm σ a ≤ N a}

theorem mem_dominatedByGauge {N : A → ℝ} {σ : TracialState A} :
    σ ∈ dominatedByGauge N ↔ ∀ a : A, tracialTwoNorm σ a ≤ N a := Iff.rfl

theorem isClosed_dominatedByGauge (N : A → ℝ) :
    IsClosed (dominatedByGauge N) := by
  have hEq : dominatedByGauge N =
      ⋂ a : A, {σ : TracialState A | tracialTwoNorm σ a ≤ N a} := by
    ext σ
    simp only [dominatedByGauge, Set.mem_setOf_eq, Set.mem_iInter]
  rw [hEq]
  refine isClosed_iInter fun a ↦ ?_
  refine isClosed_le ?_ continuous_const
  have hcont : Continuous fun σ : TracialState A ↦ (σ (star a * a)).re :=
    Complex.continuous_re.comp (continuous_tracialState_apply (star a * a))
  exact hcont.sqrt

theorem isCompact_dominatedByGauge (N : A → ℝ) :
    IsCompact (dominatedByGauge N) :=
  isCompact_of_isClosed_tracialState (isClosed_dominatedByGauge N)

/-- The square of the trace two-norm is the real part of `σ (a⋆ a)`. -/
theorem mul_self_tracialTwoNorm (σ : TracialState A) (a : A) :
    tracialTwoNorm σ a * tracialTwoNorm σ a = (σ (star a * a)).re :=
  Real.mul_self_sqrt (re_apply_star_mul_self_nonneg σ a)

theorem isConvexTraceSet_dominatedByGauge {N : A → ℝ} (hN : ∀ a, 0 ≤ N a) :
    IsConvexTraceSet (dominatedByGauge N) := by
  intro σ hσ τ hτ t ht0 ht1 a
  have h1 : (0 : ℝ) ≤ 1 - t := by linarith
  have hσa : tracialTwoNorm σ a ≤ N a := hσ a
  have hτa : tracialTwoNorm τ a ≤ N a := hτ a
  have hσsq : (σ (star a * a)).re ≤ N a * N a := by
    rw [← mul_self_tracialTwoNorm]
    exact mul_self_le_mul_self (tracialTwoNorm_nonneg σ a) hσa
  have hτsq : (τ (star a * a)).re ≤ N a * N a := by
    rw [← mul_self_tracialTwoNorm]
    exact mul_self_le_mul_self (tracialTwoNorm_nonneg τ a) hτa
  have hre : (convexComb t ht0 ht1 σ τ (star a * a)).re
      = t * (σ (star a * a)).re + (1 - t) * (τ (star a * a)).re :=
    convexComb_re t ht0 ht1 σ τ _
  have hbound : (convexComb t ht0 ht1 σ τ (star a * a)).re ≤ N a * N a := by
    rw [hre]
    have e1 : t * (σ (star a * a)).re ≤ t * (N a * N a) :=
      mul_le_mul_of_nonneg_left hσsq ht0
    have e2 : (1 - t) * (τ (star a * a)).re ≤ (1 - t) * (N a * N a) :=
      mul_le_mul_of_nonneg_left hτsq h1
    have e3 : t * (N a * N a) + (1 - t) * (N a * N a) = N a * N a := by ring
    linarith
  calc tracialTwoNorm (convexComb t ht0 ht1 σ τ) a
      = Real.sqrt ((convexComb t ht0 ht1 σ τ (star a * a)).re) := rfl
    _ ≤ Real.sqrt (N a * N a) := Real.sqrt_le_sqrt hbound
    _ = N a := Real.sqrt_mul_self (hN a)

/-- **The domination estimate.**  If `t σ + (1 - t) τ` is dominated by `N`, then
`σ` is dominated by `t^{-1/2} N`.  This is the mechanism behind CCEGSTW
Proposition 3.23(iv): a trace below a multiple of a two-continuous trace is
itself two-continuous. -/
theorem tracialTwoNorm_le_of_convexComb_mem {N : A → ℝ}
    (σ τ : TracialState A) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (h : convexComb t ht0.le ht1.le σ τ ∈ dominatedByGauge N) (a : A) :
    Real.sqrt t * tracialTwoNorm σ a ≤ N a := by
  have hτnn : (0 : ℝ) ≤ (τ (star a * a)).re :=
    re_apply_star_mul_self_nonneg τ a
  have h1 : (0 : ℝ) ≤ 1 - t := by linarith
  have hre : (convexComb t ht0.le ht1.le σ τ (star a * a)).re
      = t * (σ (star a * a)).re + (1 - t) * (τ (star a * a)).re :=
    convexComb_re t ht0.le ht1.le σ τ _
  have hle : t * (σ (star a * a)).re
      ≤ (convexComb t ht0.le ht1.le σ τ (star a * a)).re := by
    rw [hre]
    have e : 0 ≤ (1 - t) * (τ (star a * a)).re := mul_nonneg h1 hτnn
    linarith
  calc Real.sqrt t * tracialTwoNorm σ a
      = Real.sqrt (t * (σ (star a * a)).re) := by
        rw [tracialTwoNorm_def, ← Real.sqrt_mul ht0.le]
    _ ≤ Real.sqrt ((convexComb t ht0.le ht1.le σ τ (star a * a)).re) :=
        Real.sqrt_le_sqrt hle
    _ = tracialTwoNorm (convexComb t ht0.le ht1.le σ τ) a := rfl
    _ ≤ N a := h a

/-- The same estimate for the right-hand summand. -/
theorem tracialTwoNorm_le_of_convexComb_mem' {N : A → ℝ}
    (σ τ : TracialState A) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (h : convexComb t ht0.le ht1.le σ τ ∈ dominatedByGauge N) (a : A) :
    Real.sqrt (1 - t) * tracialTwoNorm τ a ≤ N a := by
  have hσnn : (0 : ℝ) ≤ (σ (star a * a)).re :=
    re_apply_star_mul_self_nonneg σ a
  have h1 : (0 : ℝ) < 1 - t := by linarith
  have hre : (convexComb t ht0.le ht1.le σ τ (star a * a)).re
      = t * (σ (star a * a)).re + (1 - t) * (τ (star a * a)).re :=
    convexComb_re t ht0.le ht1.le σ τ _
  have hle : (1 - t) * (τ (star a * a)).re
      ≤ (convexComb t ht0.le ht1.le σ τ (star a * a)).re := by
    rw [hre]
    have e : 0 ≤ t * (σ (star a * a)).re := mul_nonneg ht0.le hσnn
    linarith
  calc Real.sqrt (1 - t) * tracialTwoNorm τ a
      = Real.sqrt ((1 - t) * (τ (star a * a)).re) := by
        rw [tracialTwoNorm_def, ← Real.sqrt_mul h1.le]
    _ ≤ Real.sqrt ((convexComb t ht0.le ht1.le σ τ (star a * a)).re) :=
        Real.sqrt_le_sqrt hle
    _ = tracialTwoNorm (convexComb t ht0.le ht1.le σ τ) a := rfl
    _ ≤ N a := h a

/-- **Factoriality criterion.**  Suppose `N` is a nonnegative gauge and every
tracial state dominated by *some* multiple of `N` is already dominated by `N`.
Then `dominatedByGauge N` is a face of the trace simplex.

The hypothesis is not a formality: for a uniform tracial completion it holds
because a two-continuous trace is the canonical extension of its own
restriction, and canonical extensions are dominated by `N` with constant one. -/
theorem isFaceTraceSet_dominatedByGauge {N : A → ℝ} (hN : ∀ a, 0 ≤ N a)
    (hrescale : ∀ (σ : TracialState A) (C : ℝ), 0 < C →
      (∀ a, tracialTwoNorm σ a ≤ C * N a) → σ ∈ dominatedByGauge N) :
    IsFaceTraceSet (dominatedByGauge N) where
  isConvex := isConvexTraceSet_dominatedByGauge hN
  mem_of_convexComb_mem σ τ t ht0 ht1 h := by
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
    have hs1t : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 (by linarith)
    constructor
    · refine hrescale σ (Real.sqrt t)⁻¹ (inv_pos.2 hst) fun a ↦ ?_
      have hb := tracialTwoNorm_le_of_convexComb_mem σ τ ht0 ht1 h a
      have hmul : (Real.sqrt t)⁻¹ * (Real.sqrt t * tracialTwoNorm σ a)
          ≤ (Real.sqrt t)⁻¹ * N a :=
        mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos.2 hst))
      rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hst), one_mul] at hmul
    · refine hrescale τ (Real.sqrt (1 - t))⁻¹ (inv_pos.2 hs1t) fun a ↦ ?_
      have hb := tracialTwoNorm_le_of_convexComb_mem' σ τ ht0 ht1 h a
      have hmul : (Real.sqrt (1 - t))⁻¹ * (Real.sqrt (1 - t) * tracialTwoNorm τ a)
          ≤ (Real.sqrt (1 - t))⁻¹ * N a :=
        mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos.2 hs1t))
      rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hs1t), one_mul] at hmul

end Gauge

end

end TraciallyComplete
end GroupApproximation
