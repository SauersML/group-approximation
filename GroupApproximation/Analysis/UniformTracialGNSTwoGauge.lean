import GroupApproximation.Analysis.UniformTracialTwoNullIdeal
import GroupApproximation.Manuscript.MFRecognition.TensorSynchronizationData
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# The uniform tracial two-norm is a `TracialTwoGauge`

`Analysis/UniformTracialTwoNullIdeal` isolates the estimates which turn a
coordinate two-gauge into the audit's ideal `J` and the algebra `ℂ1 + J`:
subadditivity, the two bimodule bounds, invariance under the involution and
normalization at the unit.  It supplies one model, the operator norm, and it
records the concrete gauge
`tracialTwoSize n x = sup_{τ ∈ T(D n)} τ (x⋆ x)^{1/2}` of
`Analysis/UniformTracialSequenceCompletion` only as a `UniformTwoGauge`,
because the four missing estimates are the GNS Cauchy--Schwarz inequalities
for a bundled tracial state.

This file proves them, and closes that gap.

## The single-state layer

For one bundled `TracialState τ` on a unital C⋆-algebra `A`,

```text
tracialTwoNorm τ x = τ (x⋆ x).re ^ (1/2)
```

is realized as the seminorm of the class of `x` in Mathlib's GNS pre-Hilbert
space `(tracialStatePositiveLinearMap τ).PreGNS` (`norm_gnsClass`).  Once that
identification is in place every estimate is a Hilbert-space fact:

* `norm_apply_star_mul_le` is **Cauchy--Schwarz**,
  `‖τ (x⋆ y)‖ ≤ tracialTwoNorm τ x * tracialTwoNorm τ y`, from
  `norm_inner_le_norm` for the GNS inner product `⟪x, y⟫ = τ (x⋆ y)`
  (`inner_gnsClass`);  `norm_apply_star_mul_mul_self_le` is its squared form
  `‖τ (x⋆ y)‖² ≤ τ (x⋆ x).re · τ (y⋆ y).re`;
* `tracialTwoNorm_add_le` is **Minkowski**, from `norm_add_le`;
* `tracialTwoNorm_mul_left_le` is the left bimodule bound
  `tracialTwoNorm τ (a x) ≤ ‖a‖ · tracialTwoNorm τ x`, from the operator norm
  of Mathlib's GNS left-multiplication operator `leftMulMapPreGNS`, whose bound
  by `‖a‖` is the positivity of `‖a‖² · 1 − a⋆ a`;
* `tracialTwoNorm_star` is **traciality**, and it converts the left bimodule
  bound into the right one (`tracialTwoNorm_mul_right_le`);
* `tracialTwoNorm_one` is normalization, `τ 1 = 1`.

Nothing about the spectral order leaks out of the bridge section: every
statement above is order-free.  The positive functional is the landed
`tracialStatePositiveLinearMap`, not a parallel copy, so the `PartialOrder`
which Mathlib's GNS construction consumes is already fixed inside its type and
only the matching `StarOrderedRing` has to be re-registered; that is done with
`attribute [local instance]` on the same declaration
`tensorSynchronizationDataStarOrderedRing`, and only inside the bridge section.

## The supremum layer

Taking the supremum over all tracial states of a coordinate algebra is
compatible with each estimate (`tracialTwoSize_add_le`,
`tracialTwoSize_mul_left_le`, `tracialTwoSize_mul_right_le`,
`tracialTwoSize_star`, `tracialTwoSize_one`), because the family is bounded
above by the operator norm (`bddAbove_range_tracialTwoNorm`) and indexed by a
nonempty type.  The package is

```text
allTracesTracialTwoGauge D : TracialTwoGauge D
```

with `q = tracialTwoSize` **definitionally**, so

```text
(allTracesTracialTwoGauge D).toUniformTwoGauge = allTracesUniformTwoGauge
```

holds by `rfl`, and every landed truncation theorem of
`Analysis/UniformTracialSequenceCompletion`, together with the ideal and
`ℂ1 + J` theory of `Analysis/UniformTracialTwoNullIdeal`, now applies to the
*actual* uniform tracial two-norm rather than to an abstract gauge.  In
particular `twoNullIdeal (allTracesTracialTwoGauge D)` is the audit's `J` of
(A7) (`mem_twoNullIdeal_allTraces_iff`) and
`scalarPlusJ (allTracesTracialTwoGauge D)` is its `M = ℂ1 + J` of (A8)
(`scalarPlusJ_allTracesTracialTwoGauge`).

## Model test

`Analysis/UniformTracialTwoNullIdeal` asserts in prose that for the constant
family `D_s = ℂ` the operator-norm gauge *is* the uniform tracial two-gauge.
That is now a theorem.  Every tracial state on `ℂ` is the identity
(`tracialState_complex_eq`), so `tracialTwoSize_complex_eq_norm` computes the
gauge as the modulus and
`allTracesTracialTwoGauge_complex_eq_normTracialTwoGauge` identifies it with
`normTracialTwoGauge`.  The `ℂ` model also satisfies the audit's coordinatewise
finite-rank comparison with the printed constant `sqrt (s+1)`.

The two-by-two matrix model is *not* covered here: it needs uniqueness of the
normalized trace on `M₂`, which is a separate statement about tracial states
and is not required by anything below.
-/

namespace GroupApproximation
namespace UniformTracialGNSTwoGauge

open Filter PolarLiftingGeneralCStar
open UniformTracialSequenceCompletion UniformTracialTwoNullIdeal
open scoped ComplexOrder InnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

universe u

/-! ## The two-norm of a single tracial state -/

/-- The trace two-norm of one bundled tracial state, `‖x‖_τ = τ (x⋆ x)^{1/2}`.
The supremum of these over all tracial states of a coordinate algebra is the
gauge `tracialTwoSize` of `Analysis/UniformTracialSequenceCompletion`. -/
def tracialTwoNorm {A : Type u} [CStarAlgebra A] (τ : TracialState A) (x : A) :
    ℝ :=
  Real.sqrt ((τ (star x * x)).re)

theorem tracialTwoNorm_def {A : Type u} [CStarAlgebra A]
    (τ : TracialState A) (x : A) :
    tracialTwoNorm τ x = Real.sqrt ((τ (star x * x)).re) := rfl

theorem tracialTwoNorm_nonneg {A : Type u} [CStarAlgebra A]
    (τ : TracialState A) (x : A) : 0 ≤ tracialTwoNorm τ x :=
  Real.sqrt_nonneg _

@[simp] theorem tracialTwoNorm_zero {A : Type u} [CStarAlgebra A]
    (τ : TracialState A) : tracialTwoNorm τ (0 : A) = 0 := by
  rw [tracialTwoNorm_def, mul_zero, TracialState.map_zero, Complex.zero_re,
    Real.sqrt_zero]

/-- A tracial state is nonnegative on `x⋆ x`, in the real form used below. -/
theorem re_apply_star_mul_self_nonneg {A : Type u} [CStarAlgebra A]
    (τ : TracialState A) (x : A) : 0 ≤ (τ (star x * x)).re :=
  (Complex.nonneg_iff.mp (τ.map_star_mul_self_nonneg x)).1

/-- The trace two-norm is dominated by the operator norm.  This is the
single-state form of the landed `tracialTwoSize_le_norm`; it is reproved here
because the landed argument is a `private` lemma of the completion module. -/
theorem tracialTwoNorm_le_norm {A : Type u} [CStarAlgebra A]
    (τ : TracialState A) (x : A) : tracialTwoNorm τ x ≤ ‖x‖ := by
  have hsq : (τ (star x * x)).re ≤ ‖x‖ ^ 2 := by
    calc (τ (star x * x)).re ≤ ‖τ (star x * x)‖ := Complex.re_le_norm _
      _ ≤ ‖star x * x‖ :=
          Manuscript.MFRecognition.TensorSynchronization.norm_tracialState_le
            τ (star x * x)
      _ = ‖x‖ ^ 2 := by rw [CStarRing.norm_star_mul_self, pow_two]
  calc tracialTwoNorm τ x = Real.sqrt ((τ (star x * x)).re) := rfl
    _ ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg x)

/-- **Traciality**: the trace two-norm is invariant under the involution.
This is the one estimate which needs no analysis at all. -/
theorem tracialTwoNorm_star {A : Type u} [CStarAlgebra A]
    (τ : TracialState A) (x : A) :
    tracialTwoNorm τ (star x) = tracialTwoNorm τ x := by
  have h : τ (x * star x) = τ (star x * x) := τ.map_mul_comm x (star x)
  simp only [tracialTwoNorm_def, star_star]
  rw [h]

/-- **Normalization**: a tracial state is a state. -/
@[simp] theorem tracialTwoNorm_one {A : Type u} [CStarAlgebra A]
    (τ : TracialState A) : tracialTwoNorm τ (1 : A) = 1 := by
  simp only [tracialTwoNorm_def, star_one, one_mul, TracialState.apply_one,
    Complex.one_re, Real.sqrt_one]

/-- The family of trace two-norms of one element is bounded above by its
operator norm, so the supremum defining `tracialTwoSize` is a genuine
supremum. -/
theorem bddAbove_range_tracialTwoNorm {A : Type u} [CStarAlgebra A] (x : A) :
    BddAbove (Set.range fun τ : TracialState A ↦ tracialTwoNorm τ x) := by
  refine ⟨‖x‖, ?_⟩
  rintro _ ⟨τ, rfl⟩
  exact tracialTwoNorm_le_norm τ x

/-! ## The GNS bridge

Mathlib's GNS construction consumes a `PositiveLinearMap`, hence a
`PartialOrder` and a `StarOrderedRing` structure on the algebra.  The positive
functional attached to a tracial state is the landed
`tracialStatePositiveLinearMap`, whose type already carries the spectral
`PartialOrder`, so only the matching `StarOrderedRing` has to be registered,
and it is registered locally and only inside this section.  Every statement
proved here is order-free. -/

section GNSBridge

open Manuscript.MFRecognition.TensorSynchronization

attribute [local instance] tensorSynchronizationDataPartialOrder
attribute [local instance] tensorSynchronizationDataStarOrderedRing

variable {A : Type u} [CStarAlgebra A]

/-- The class of `x` in the GNS pre-Hilbert space of a tracial state. -/
def gnsClass (τ : TracialState A) (x : A) :
    (tracialStatePositiveLinearMap τ).PreGNS :=
  (tracialStatePositiveLinearMap τ).toPreGNS x

theorem gnsClass_def (τ : TracialState A) (x : A) :
    gnsClass τ x = (tracialStatePositiveLinearMap τ).toPreGNS x := rfl

theorem gnsClass_add (τ : TracialState A) (x y : A) :
    gnsClass τ (x + y) = gnsClass τ x + gnsClass τ y := by
  simp only [gnsClass_def]
  exact map_add _ x y

/-- **The GNS seminorm computes the trace two-norm.** -/
theorem norm_gnsClass (τ : TracialState A) (x : A) :
    ‖gnsClass τ x‖ = tracialTwoNorm τ x := by
  rw [gnsClass_def, PositiveLinearMap.preGNS_norm_def,
    PositiveLinearMap.ofPreGNS_toPreGNS, tracialStatePositiveLinearMap_apply,
    tracialTwoNorm_def]

/-- **The GNS inner product is the sesquilinear form of the trace.** -/
theorem inner_gnsClass (τ : TracialState A) (x y : A) :
    ⟪gnsClass τ x, gnsClass τ y⟫_ℂ = τ (star x * y) := by
  rw [gnsClass_def, gnsClass_def, PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS, PositiveLinearMap.ofPreGNS_toPreGNS,
    tracialStatePositiveLinearMap_apply]

/-- **GNS Cauchy--Schwarz for a bundled tracial state**:
`|τ (x⋆ y)| ≤ τ (x⋆ x)^{1/2} · τ (y⋆ y)^{1/2}`. -/
theorem norm_apply_star_mul_le (τ : TracialState A) (x y : A) :
    ‖τ (star x * y)‖ ≤ tracialTwoNorm τ x * tracialTwoNorm τ y := by
  rw [← inner_gnsClass τ x y, ← norm_gnsClass τ x, ← norm_gnsClass τ y]
  exact norm_inner_le_norm _ _

/-- **GNS Cauchy--Schwarz, squared form**: `|τ (x⋆ y)|² ≤ τ (x⋆ x) · τ (y⋆ y)`,
the inequality named in the audit. -/
theorem norm_apply_star_mul_mul_self_le (τ : TracialState A) (x y : A) :
    ‖τ (star x * y)‖ * ‖τ (star x * y)‖
      ≤ (τ (star x * x)).re * (τ (star y * y)).re := by
  have hx : (0 : ℝ) ≤ (τ (star x * x)).re := re_apply_star_mul_self_nonneg τ x
  have hy : (0 : ℝ) ≤ (τ (star y * y)).re := re_apply_star_mul_self_nonneg τ y
  calc ‖τ (star x * y)‖ * ‖τ (star x * y)‖
      ≤ (tracialTwoNorm τ x * tracialTwoNorm τ y)
        * (tracialTwoNorm τ x * tracialTwoNorm τ y) :=
        mul_self_le_mul_self (norm_nonneg _) (norm_apply_star_mul_le τ x y)
    _ = (Real.sqrt ((τ (star x * x)).re) * Real.sqrt ((τ (star x * x)).re))
        * (Real.sqrt ((τ (star y * y)).re)
          * Real.sqrt ((τ (star y * y)).re)) := by
        simp only [tracialTwoNorm_def]
        ring
    _ = (τ (star x * x)).re * (τ (star y * y)).re := by
        rw [Real.mul_self_sqrt hx, Real.mul_self_sqrt hy]

/-- **Minkowski for the trace two-norm**, the `add_le` field of
`TracialTwoGauge`. -/
theorem tracialTwoNorm_add_le (τ : TracialState A) (x y : A) :
    tracialTwoNorm τ (x + y) ≤ tracialTwoNorm τ x + tracialTwoNorm τ y := by
  have h : ‖gnsClass τ (x + y)‖ ≤ ‖gnsClass τ x‖ + ‖gnsClass τ y‖ := by
    rw [gnsClass_add]
    exact norm_add_le _ _
  rwa [norm_gnsClass, norm_gnsClass, norm_gnsClass] at h

/-- GNS left multiplication is left multiplication in the algebra. -/
theorem leftMulMapPreGNS_gnsClass (τ : TracialState A) (a x : A) :
    (tracialStatePositiveLinearMap τ).leftMulMapPreGNS a (gnsClass τ x)
      = gnsClass τ (a * x) := by
  rw [gnsClass_def, gnsClass_def]
  show (tracialStatePositiveLinearMap τ).toPreGNS
      (a * (tracialStatePositiveLinearMap τ).ofPreGNS
        ((tracialStatePositiveLinearMap τ).toPreGNS x))
    = (tracialStatePositiveLinearMap τ).toPreGNS (a * x)
  rw [PositiveLinearMap.ofPreGNS_toPreGNS]

/-- **The left bimodule bound**, the `mul_left_le` field of `TracialTwoGauge`.
The operator-norm bound on GNS left multiplication is the positivity of
`‖a‖² · 1 − a⋆ a`. -/
theorem tracialTwoNorm_mul_left_le (τ : TracialState A) (a x : A) :
    tracialTwoNorm τ (a * x) ≤ ‖a‖ * tracialTwoNorm τ x := by
  have hop : ‖(tracialStatePositiveLinearMap τ).leftMulMapPreGNS a‖ ≤ ‖a‖ :=
    LinearMap.mkContinuous_norm_le _ (norm_nonneg a) _
  have h : ‖gnsClass τ (a * x)‖ ≤ ‖a‖ * ‖gnsClass τ x‖ := by
    calc ‖gnsClass τ (a * x)‖
        = ‖(tracialStatePositiveLinearMap τ).leftMulMapPreGNS a
            (gnsClass τ x)‖ := by rw [leftMulMapPreGNS_gnsClass]
      _ ≤ ‖(tracialStatePositiveLinearMap τ).leftMulMapPreGNS a‖
            * ‖gnsClass τ x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖a‖ * ‖gnsClass τ x‖ :=
          mul_le_mul_of_nonneg_right hop (norm_nonneg _)
  rwa [norm_gnsClass, norm_gnsClass] at h

end GNSBridge

/-- **The right bimodule bound**, the `mul_right_le` field of
`TracialTwoGauge`.  It is the left bound read through traciality. -/
theorem tracialTwoNorm_mul_right_le {A : Type u} [CStarAlgebra A]
    (τ : TracialState A) (x a : A) :
    tracialTwoNorm τ (x * a) ≤ tracialTwoNorm τ x * ‖a‖ := by
  have h1 : tracialTwoNorm τ (x * a) = tracialTwoNorm τ (star a * star x) := by
    rw [← tracialTwoNorm_star τ (x * a), star_mul]
  have h2 : tracialTwoNorm τ (star a * star x)
      ≤ ‖star a‖ * tracialTwoNorm τ (star x) :=
    tracialTwoNorm_mul_left_le τ (star a) (star x)
  rw [norm_star, tracialTwoNorm_star] at h2
  rw [h1, mul_comm (tracialTwoNorm τ x) ‖a‖]
  exact h2

/-! ## The supremum over all tracial states -/

section SupGauge

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)] [∀ n, Nontrivial (D n)]

/-- The landed coordinate gauge is the supremum of the single-state two-norms.
This is a definitional unfolding, recorded so that the estimates above can be
transported to `tracialTwoSize` by rewriting. -/
theorem tracialTwoSize_eq_sSup (n : ℕ) (x : D n) :
    tracialTwoSize n x
      = sSup (Set.range fun τ : TracialState (D n) ↦ tracialTwoNorm τ x) :=
  rfl

variable [∀ n, Nonempty (TracialState (D n))]

theorem tracialTwoNorm_le_tracialTwoSize (n : ℕ) (τ : TracialState (D n))
    (x : D n) : tracialTwoNorm τ x ≤ tracialTwoSize n x := by
  rw [tracialTwoSize_eq_sSup]
  exact le_csSup (bddAbove_range_tracialTwoNorm x) (Set.mem_range_self τ)

/-- **Minkowski for the uniform tracial two-gauge.** -/
theorem tracialTwoSize_add_le (n : ℕ) (x y : D n) :
    tracialTwoSize n (x + y) ≤ tracialTwoSize n x + tracialTwoSize n y := by
  rw [tracialTwoSize_eq_sSup]
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨τ, rfl⟩
  exact (tracialTwoNorm_add_le τ x y).trans
    (add_le_add (tracialTwoNorm_le_tracialTwoSize n τ x)
      (tracialTwoNorm_le_tracialTwoSize n τ y))

/-- **The left bimodule bound for the uniform tracial two-gauge.** -/
theorem tracialTwoSize_mul_left_le (n : ℕ) (a x : D n) :
    tracialTwoSize n (a * x) ≤ ‖a‖ * tracialTwoSize n x := by
  rw [tracialTwoSize_eq_sSup]
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨τ, rfl⟩
  exact (tracialTwoNorm_mul_left_le τ a x).trans
    (mul_le_mul_of_nonneg_left (tracialTwoNorm_le_tracialTwoSize n τ x)
      (norm_nonneg a))

/-- **The right bimodule bound for the uniform tracial two-gauge.** -/
theorem tracialTwoSize_mul_right_le (n : ℕ) (x a : D n) :
    tracialTwoSize n (x * a) ≤ tracialTwoSize n x * ‖a‖ := by
  rw [tracialTwoSize_eq_sSup]
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨τ, rfl⟩
  exact (tracialTwoNorm_mul_right_le τ x a).trans
    (mul_le_mul_of_nonneg_right (tracialTwoNorm_le_tracialTwoSize n τ x)
      (norm_nonneg a))

/-- **Traciality for the uniform tracial two-gauge.** -/
theorem tracialTwoSize_star (n : ℕ) (x : D n) :
    tracialTwoSize n (star x) = tracialTwoSize n x := by
  have hfun : (fun τ : TracialState (D n) ↦ tracialTwoNorm τ (star x))
      = fun τ : TracialState (D n) ↦ tracialTwoNorm τ x := by
    funext τ
    exact tracialTwoNorm_star τ x
  rw [tracialTwoSize_eq_sSup, tracialTwoSize_eq_sSup, hfun]

/-- **Normalization for the uniform tracial two-gauge.**  This is the field
which `Analysis/UniformTracialTwoNullIdeal` shows is load-bearing: without it
`ℂ1 + J` collapses to the whole bounded product. -/
theorem tracialTwoSize_one (n : ℕ) : tracialTwoSize n (1 : D n) = 1 := by
  have hfun : (fun τ : TracialState (D n) ↦ tracialTwoNorm τ (1 : D n))
      = fun _ : TracialState (D n) ↦ (1 : ℝ) := by
    funext τ
    exact tracialTwoNorm_one τ
  rw [tracialTwoSize_eq_sSup, hfun, Set.range_const, csSup_singleton]

end SupGauge

/-! ## The package -/

/-- **The uniform tracial two-gauge, as a `TracialTwoGauge`.**

Its `q` field is the landed `tracialTwoSize`, the supremum over all bundled
tracial states of the coordinate algebras.  This is the declaration whose
absence was the named residue of the completion lane: with it, the ideal `J`,
the algebra `ℂ1 + J`, uniqueness of the scalar part, and the closedness
statements of `Analysis/UniformTracialTwoNullIdeal` all hold for the actual
uniform tracial two-norm. -/
def allTracesTracialTwoGauge (D : ℕ → Type u) [∀ n, CStarAlgebra (D n)]
    [∀ n, Nontrivial (D n)] [∀ n, Nonempty (TracialState (D n))] :
    TracialTwoGauge D where
  q := tracialTwoSize
  zero := tracialTwoSize_zero
  nonneg := tracialTwoSize_nonneg
  le_norm := tracialTwoSize_le_norm
  add_le := tracialTwoSize_add_le
  mul_left_le := tracialTwoSize_mul_left_le
  mul_right_le := tracialTwoSize_mul_right_le
  star_eq := tracialTwoSize_star
  one_eq := tracialTwoSize_one

section Package

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)] [∀ n, Nontrivial (D n)]
  [∀ n, Nonempty (TracialState (D n))]

@[simp] theorem allTracesTracialTwoGauge_q (n : ℕ) (x : D n) :
    (allTracesTracialTwoGauge D).q n x = tracialTwoSize n x := rfl

/-- **The upgrade is definitionally the landed gauge**, so every theorem of
`Analysis/UniformTracialSequenceCompletion` stated for
`allTracesUniformTwoGauge` applies verbatim. -/
theorem allTracesTracialTwoGauge_toUniformTwoGauge :
    (allTracesTracialTwoGauge D).toUniformTwoGauge = allTracesUniformTwoGauge :=
  rfl

/-- The audit's `J` of (A7), for the actual uniform tracial two-norm. -/
theorem mem_twoNullIdeal_allTraces_iff {x : BoundedCStarSequence D} :
    x ∈ twoNullIdeal (allTracesTracialTwoGauge D) ↔
      Tendsto (fun n ↦ tracialTwoSize n (x n)) atTop (nhds 0) :=
  Iff.rfl

/-- The audit's `M = ℂ1 + J` of (A8) is the set already shown in
`Analysis/UniformTracialSequenceCompletion` to be uniformly two-approximable by
scalar truncations from the unitized `c₀`-sum. -/
theorem scalarPlusJ_allTracesTracialTwoGauge :
    scalarPlusJ (allTracesTracialTwoGauge D)
      = scalarPlusTwoNull (allTracesUniformTwoGauge (D := D)) := by
  rw [scalarPlusJ_eq_scalarPlusTwoNull,
    allTracesTracialTwoGauge_toUniformTwoGauge]

/-- The audit's `h ∈ J \ B` of (A1) and (A10), now for the actual uniform
tracial two-norm: an obstruction whose recorded coordinate two-size is the
genuine tracial one lies in `J` and not in the `c₀` sum, so `J` is strictly
larger than `⊕_s D_s`. -/
theorem obstruction_mem_twoNullIdeal_allTraces
    (B : CuntzPedersenCoronaObstruction.TraciallyNullObstruction D)
    (hq : B.twoSize = tracialTwoSize) :
    B.toBlockObstruction.sequence ∈ twoNullIdeal (allTracesTracialTwoGauge D) ∧
      B.toBlockObstruction.sequence ∉ nullCStarSequenceIdeal D atTop :=
  obstruction_mem_twoNullIdeal_not_mem_nullIdeal (allTracesTracialTwoGauge D) B hq

end Package

/-! ## Model test: the constant family `D_s = ℂ` -/

/-- The constant family of coordinate algebras `D_s = ℂ`. -/
abbrev complexBlocks : ℕ → Type := fun _ ↦ ℂ

/-- The identity is a tracial state on `ℂ`. -/
def complexTracialState : TracialState ℂ where
  toLinearMap := LinearMap.id
  map_one := rfl
  map_star_mul_self_nonneg z := by
    show (0 : ℂ) ≤ star z * z
    exact star_mul_self_nonneg z
  map_mul_comm x y := by
    show x * y = y * x
    exact mul_comm x y

instance instNonemptyTracialStateComplex : Nonempty (TracialState ℂ) :=
  ⟨complexTracialState⟩

/-- **`ℂ` has exactly one tracial state, the identity.**  A tracial state is
`ℂ`-linear and unital, so it is determined by its value on `z = z · 1`. -/
theorem tracialState_complex_eq (τ : TracialState ℂ) (z : ℂ) : τ z = z := by
  have h : τ (z • (1 : ℂ)) = z • τ (1 : ℂ) := τ.map_smul z 1
  simpa using h

/-- **The model test at one state**: the trace two-norm of `ℂ` is the
modulus. -/
theorem tracialTwoNorm_complex (τ : TracialState ℂ) (z : ℂ) :
    tracialTwoNorm τ z = ‖z‖ := by
  have hpos : (0 : ℂ) ≤ star z * z := star_mul_self_nonneg z
  have hre : (star z * z).re = ‖z‖ ^ 2 := by
    rw [Complex.re_eq_norm.mpr hpos, CStarRing.norm_star_mul_self, pow_two]
  rw [tracialTwoNorm_def, tracialState_complex_eq, hre,
    Real.sqrt_sq (norm_nonneg z)]

/-- **The model test.**  For the constant family `D_s = ℂ` the uniform tracial
two-gauge is the modulus in every coordinate, so the abstract gauge is faithful
rather than degenerate. -/
theorem tracialTwoSize_complex_eq_norm (n : ℕ) (z : ℂ) :
    tracialTwoSize (D := complexBlocks) n z = ‖z‖ := by
  have hfun : (fun τ : TracialState (complexBlocks n) ↦ tracialTwoNorm τ z)
      = fun _ : TracialState (complexBlocks n) ↦ ‖z‖ := by
    funext τ
    exact tracialTwoNorm_complex τ z
  rw [tracialTwoSize_eq_sSup, hfun, Set.range_const, csSup_singleton]

theorem allTracesTracialTwoGauge_complex_q (n : ℕ) (z : ℂ) :
    (allTracesTracialTwoGauge complexBlocks).q n z = ‖z‖ :=
  tracialTwoSize_complex_eq_norm n z

/-- **The prose claim of `Analysis/UniformTracialTwoNullIdeal`, proved**: for
the constant family `D_s = ℂ` the operator-norm gauge *is* the uniform tracial
two-gauge. -/
theorem allTracesTracialTwoGauge_complex_eq_normTracialTwoGauge :
    (allTracesTracialTwoGauge complexBlocks).q
      = (normTracialTwoGauge complexBlocks).q := by
  funext n z
  rw [allTracesTracialTwoGauge_complex_q, normTracialTwoGauge_q]

/-- The `ℂ` model satisfies the audit's coordinatewise finite-rank comparison
with the printed constant `sqrt (s+1)`, so that hypothesis is consistent with
the genuine tracial gauge and not only with the operator-norm model. -/
theorem allTracesTracialTwoGauge_complex_isCoordinateNormComparison :
    IsCoordinateNormComparison (allTracesTracialTwoGauge complexBlocks)
      sqrtSuccBound := by
  intro n z
  rw [allTracesTracialTwoGauge_complex_q]
  calc ‖z‖ = 1 * ‖z‖ := (one_mul _).symm
    _ ≤ sqrtSuccBound n * ‖z‖ :=
        mul_le_mul_of_nonneg_right (one_le_sqrtSuccBound n) (norm_nonneg z)

end

end UniformTracialGNSTwoGauge
end GroupApproximation
