import GroupApproximation.Analysis.TraciallyCompleteCStar
import GroupApproximation.Analysis.STW22CanonicalTraceExtension

/-!
# The uniform tracial completion is a factorial pair

STW Problem XXII asks about **factorial tracially complete** pairs `(M, X)`.
This file supplies the factoriality half for the pair produced by this
project's uniform tracial completion, in the form CCEGSTW Definition 3.13
demands: `X` is a closed face of `T(M)`.

The designated trace set is

    designatedTraces hr = {σ | ∀ z, ‖z‖_{2,σ} ≤ ‖z‖_{2,T(A)}},

the tracial states of the completion dominated by the completion gauge.  Three
theorems make this the right set and give it the three properties:

* `designatedTraces_eq_range`: it is exactly the range of `canonicalExtension`,
  i.e. exactly the traces induced from `T(A)` -- so nothing has been quietly
  enlarged or shrunk;
* `mem_designatedTraces_iff_isCompletionUniformTwoContinuous`: it is exactly the
  set of uniform-two-continuous traces, which is CCEGSTW Proposition 3.15 in
  this concrete setting;
* `isFaceTraceSet_designatedTraces`, `isClosed_designatedTraces`: it is a closed
  face, which is factoriality.

The proof of the face property is CCEGSTW's, specialised: if
`t σ₁ + (1 - t) σ₂` is dominated by the gauge then `σ_i` is dominated by
`t^{-1/2}` times the gauge, hence is uniform-two continuous, hence -- by
density of the base algebra -- is the canonical extension of its own
restriction, hence lies in the set with constant one.

This is the specialisation to `X = T(A)` of CCEGSTW Proposition 3.23(iv),
"`(Ā^X, X̃)` is factorial if and only if `X` is a face in `T(A)`": here `X` is
all of `T(A)`, which is trivially a face of itself, so factoriality is a
theorem and not a hypothesis that has to be assumed.
-/

namespace GroupApproximation
namespace STW22FactorialCore

open Filter PolarLiftingGeneralCStar
open UniformTracialSequenceCompletion UniformTracialTwoNullIdeal
open UniformTracialCompletionIdentification
open UniformTracialBoundedCauchyQuotient
open UniformTracialGNSTwoGauge STW22Assembly
open STW22ActualTraceSpaces STW22BaseUniformTracialGauge
open STW22CanonicalTraceExtension
open TraciallyComplete

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)] [∀ n, Nonempty (TracialState (D n))]

/-! ## The realization is a star-algebra map -/

/-- `realize` is the underlying map of the realization star-algebra equivalence.
This is the defeq that `canonicalExtension_apply` already relies on; it is
isolated here so that the three transport lemmas below fail loudly if it ever
stops holding. -/
theorem realize_eq_coe {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r)
    (x : BoundedUniformTwoCompletion (G D) r hr) :
    realize (G D) hr x = realizationStarAlgEquiv (G D) hr x := rfl

theorem realize_sub {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r)
    (x y : BoundedUniformTwoCompletion (G D) r hr) :
    realize (G D) hr (x - y) = realize (G D) hr x - realize (G D) hr y := by
  rw [realize_eq_coe, realize_eq_coe, realize_eq_coe]
  exact map_sub (realizationStarAlgEquiv (G D) hr) x y

theorem realize_mul' {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r)
    (x y : BoundedUniformTwoCompletion (G D) r hr) :
    realize (G D) hr (x * y) = realize (G D) hr x * realize (G D) hr y := by
  rw [realize_eq_coe, realize_eq_coe, realize_eq_coe]
  exact map_mul (realizationStarAlgEquiv (G D) hr) x y

theorem realize_star' {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r)
    (x : BoundedUniformTwoCompletion (G D) r hr) :
    realize (G D) hr (Star.star x) = Star.star (realize (G D) hr x) := by
  rw [realize_eq_coe, realize_eq_coe]
  exact map_star (realizationStarAlgEquiv (G D) hr) x

/-! ## The completion gauge -/

/-- The uniform two-norm `‖·‖_{2,T(A)}` of the base algebra, read on the bounded
uniform-two completion through its realization in `ℂ1 + J`.  This is the gauge
with respect to which the completion was formed. -/
def completionGauge {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r)
    (x : BoundedUniformTwoCompletion (G D) r hr) : ℝ :=
  uniformTwoNorm (G D) ((realize (G D) hr x).1 : BoundedCStarSequence D)

theorem completionGauge_nonneg {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r)
    (x : BoundedUniformTwoCompletion (G D) r hr) :
    0 ≤ completionGauge hr x :=
  uniformTwoNorm_nonneg _ _

/-- The completion gauge of a difference from a base element is the uniform
two-distance used by `BaseApproximation`. -/
theorem completionGauge_sub_baseToCompletion {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r)
    (x : BoundedUniformTwoCompletion (G D) r hr) (b : BaseAlgebra D) :
    completionGauge hr (x - baseToCompletion (G D) hr b)
      = uniformTwoNorm (G D)
          (((realize (G D) hr x - baseToScalarPlusJ (G D) b : M D) :
            BoundedCStarSequence D)) := by
  rw [completionGauge, realize_sub, realize_baseToCompletion]
  rfl

/-! ## Convergence along a bounded base approximation -/

theorem uniformTwoNorm_le_sub_add (u v : BoundedCStarSequence D) :
    uniformTwoNorm (G D) u
      ≤ uniformTwoNorm (G D) (u - v) + uniformTwoNorm (G D) v := by
  have h := uniformTwoNorm_sub_triangle u v 0
  rwa [sub_zero, sub_zero] at h

/-- The gauges of a bounded base approximation converge to the gauge of the
limit. -/
theorem tendsto_uniformTwoNorm_baseApproximation (y : M D)
    (A : BaseApproximation y) :
    Tendsto (fun k ↦ uniformTwoNorm (G D) (A.seq k).1) atTop
      (nhds (uniformTwoNorm (G D) y.1)) := by
  have hcoe : ∀ k : ℕ,
      ((y - baseToScalarPlusJ (G D) (A.seq k) : M D) : BoundedCStarSequence D)
        = y.1 - (A.seq k).1 := by
    intro k
    rw [coe_sub_M]
    rfl
  have hd : ∀ k : ℕ,
      ‖uniformTwoNorm (G D) (A.seq k).1 - uniformTwoNorm (G D) y.1‖
        ≤ uniformTwoNorm (G D)
            ((y - baseToScalarPlusJ (G D) (A.seq k) : M D) :
              BoundedCStarSequence D) := by
    intro k
    rw [hcoe k, Real.norm_eq_abs]
    have h1 := uniformTwoNorm_le_sub_add (A.seq k).1 y.1
    have h2 := uniformTwoNorm_le_sub_add y.1 (A.seq k).1
    have hsym : uniformTwoNorm (G D) ((A.seq k).1 - y.1)
        = uniformTwoNorm (G D) (y.1 - (A.seq k).1) :=
      uniformTwoNorm_sub_comm _ _
    rw [hsym] at h1
    rw [abs_le]
    constructor <;> linarith
  have hzero : Tendsto (fun k ↦ uniformTwoNorm (G D) (A.seq k).1
      - uniformTwoNorm (G D) y.1) atTop (nhds 0) :=
    squeeze_zero_norm hd A.tendsto_two
  have hconst : Tendsto (fun _ : ℕ ↦ uniformTwoNorm (G D) y.1) atTop
      (nhds (uniformTwoNorm (G D) y.1)) := tendsto_const_nhds
  have hsum := hzero.add hconst
  simpa using hsum

/-- Along any bounded base approximation the trace two-norms converge to the
trace two-norm of the model extension. -/
theorem tendsto_tracialTwoNorm_modelExtension
    (tau : TracialState (BaseAlgebra D)) (y : M D) (A : BaseApproximation y) :
    Tendsto (fun k ↦ tracialTwoNorm tau (A.seq k)) atTop
      (nhds (tracialTwoNorm (modelExtension tau) y)) := by
  have hlim : Tendsto (fun k ↦ tau (Star.star (A.seq k) * A.seq k)) atTop
      (nhds (modelExtension tau (Star.star y * y))) :=
    trace_tendsto_extensionValue tau (Star.star y * y) (A.star.mul A)
  have hre : Tendsto (fun k ↦ (tau (Star.star (A.seq k) * A.seq k)).re) atTop
      (nhds ((modelExtension tau (Star.star y * y)).re)) :=
    (Complex.continuous_re.tendsto _).comp hlim
  exact hre.sqrt

/-- **The model extension is dominated by the gauge.**  This is CCEGSTW (3.27):
`‖a‖_{2,τ̃} ≤ ‖a‖_{2,X}`. -/
theorem tracialTwoNorm_modelExtension_le
    (tau : TracialState (BaseAlgebra D)) (y : M D) :
    tracialTwoNorm (modelExtension tau) y ≤ uniformTwoNorm (G D) y.1 := by
  refine le_of_tendsto_of_tendsto'
    (tendsto_tracialTwoNorm_modelExtension tau y (chosenApproximation y))
    (tendsto_uniformTwoNorm_baseApproximation y (chosenApproximation y))
    (fun k ↦ ?_)
  exact tracialTwoNorm_le_uniformTwoNorm_allTraces tau ((chosenApproximation y).seq k)

/-- Every canonical extension is dominated by the completion gauge. -/
theorem tracialTwoNorm_canonicalExtension_le {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r)
    (tau : TracialState (BaseAlgebra D))
    (x : BoundedUniformTwoCompletion (G D) r hr) :
    tracialTwoNorm (canonicalExtension hr tau) x ≤ completionGauge hr x := by
  have hval : canonicalExtension hr tau (Star.star x * x)
      = modelExtension tau
          (Star.star (realize (G D) hr x) * realize (G D) hr x) := by
    rw [canonicalExtension_apply, realize_mul', realize_star']
  calc tracialTwoNorm (canonicalExtension hr tau) x
      = Real.sqrt ((canonicalExtension hr tau (Star.star x * x)).re) := rfl
    _ = Real.sqrt ((modelExtension tau
          (Star.star (realize (G D) hr x) * realize (G D) hr x)).re) := by
        rw [hval]
    _ = tracialTwoNorm (modelExtension tau) (realize (G D) hr x) := rfl
    _ ≤ uniformTwoNorm (G D) (realize (G D) hr x).1 :=
        tracialTwoNorm_modelExtension_le tau _
    _ = completionGauge hr x := rfl

/-! ## Density: a two-continuous trace is a canonical extension -/

/-- **Uniqueness of two-continuous extensions.**  A uniform-two-continuous
tracial state of the completion is the canonical extension of its own
restriction to the base algebra.  The base algebra is uniform-two dense, which
is exactly the content of `chosenApproximation`. -/
theorem eq_canonicalExtension_of_continuous {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r)
    (σ : TracialState (BoundedUniformTwoCompletion (G D) r hr))
    (hcont : IsCompletionUniformTwoContinuous (G D) hr σ) :
    σ = canonicalExtension hr (restrictToBase (G D) hr σ) := by
  refine tracialState_ext fun x ↦ ?_
  have hgauge : ∀ k : ℕ,
      uniformTwoNorm (G D)
          ((realize (G D) hr (x - baseToCompletion (G D) hr
            ((chosenApproximation (realize (G D) hr x)).seq k))).1 :
            BoundedCStarSequence D)
        = uniformTwoNorm (G D)
            (((realize (G D) hr x - baseToScalarPlusJ (G D)
              ((chosenApproximation (realize (G D) hr x)).seq k) : M D) :
              BoundedCStarSequence D)) := by
    intro k
    exact completionGauge_sub_baseToCompletion hr x _
  have hnull : Tendsto (fun k ↦ uniformTwoNorm (G D)
      ((realize (G D) hr (x - baseToCompletion (G D) hr
        ((chosenApproximation (realize (G D) hr x)).seq k))).1 :
        BoundedCStarSequence D)) atTop (nhds 0) := by
    have hfun : (fun k ↦ uniformTwoNorm (G D)
        ((realize (G D) hr (x - baseToCompletion (G D) hr
          ((chosenApproximation (realize (G D) hr x)).seq k))).1 :
          BoundedCStarSequence D)) =
        fun k ↦ uniformTwoNorm (G D)
          (((realize (G D) hr x - baseToScalarPlusJ (G D)
            ((chosenApproximation (realize (G D) hr x)).seq k) : M D) :
            BoundedCStarSequence D)) := funext hgauge
    rw [hfun]
    exact (chosenApproximation (realize (G D) hr x)).tendsto_two
  have hdiff := hcont
    (fun k ↦ x - baseToCompletion (G D) hr
      ((chosenApproximation (realize (G D) hr x)).seq k)) hnull
  have hsplit : (fun k ↦ σ (x - baseToCompletion (G D) hr
      ((chosenApproximation (realize (G D) hr x)).seq k)))
      = fun k ↦ σ x - restrictToBase (G D) hr σ
        ((chosenApproximation (realize (G D) hr x)).seq k) := by
    funext k
    rw [TracialState.map_sub]
    rfl
  rw [hsplit] at hdiff
  have hconst : Tendsto (fun _ : ℕ ↦ σ x) atTop (nhds (σ x)) :=
    tendsto_const_nhds
  have hto : Tendsto (fun k ↦ restrictToBase (G D) hr σ
      ((chosenApproximation (realize (G D) hr x)).seq k)) atTop (nhds (σ x)) := by
    have := hconst.sub hdiff
    simpa using this
  have hext := trace_tendsto_extensionValue (restrictToBase (G D) hr σ)
    (realize (G D) hr x) (chosenApproximation (realize (G D) hr x))
  exact tendsto_nhds_unique hto hext

/-! ## The designated trace set and its factoriality -/

/-- **The designated traces of the uniform tracial completion**: the tracial
states dominated by the completion gauge.  `designatedTraces_eq_range` proves
that this is exactly the set of traces induced from `T(A)`. -/
def designatedTraces {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r) :
    Set (TracialState (BoundedUniformTwoCompletion (G D) r hr)) :=
  dominatedByGauge (completionGauge hr)

theorem mem_designatedTraces_iff {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r)
    (σ : TracialState (BoundedUniformTwoCompletion (G D) r hr)) :
    σ ∈ designatedTraces hr ↔ ∀ z, tracialTwoNorm σ z ≤ completionGauge hr z :=
  Iff.rfl

/-- A trace dominated by any multiple of the gauge is uniform-two continuous. -/
theorem isCompletionUniformTwoContinuous_of_bounded {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r)
    (σ : TracialState (BoundedUniformTwoCompletion (G D) r hr)) {C : ℝ}
    (hC : ∀ z, tracialTwoNorm σ z ≤ C * completionGauge hr z) :
    IsCompletionUniformTwoContinuous (G D) hr σ := by
  intro x hx
  refine squeeze_zero_norm
    (fun N ↦ (norm_apply_le_tracialTwoNorm σ (x N)).trans (hC (x N))) ?_
  simpa using hx.const_mul C

/-- **The designated traces are exactly the uniform-two-continuous traces.**
This is CCEGSTW Proposition 3.15 for this pair. -/
theorem mem_designatedTraces_iff_isCompletionUniformTwoContinuous {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r)
    (σ : TracialState (BoundedUniformTwoCompletion (G D) r hr)) :
    σ ∈ designatedTraces hr ↔ IsCompletionUniformTwoContinuous (G D) hr σ := by
  constructor
  · intro hσ
    refine isCompletionUniformTwoContinuous_of_bounded hr σ (C := 1) ?_
    intro z
    rw [one_mul]
    exact hσ z
  · intro hcont
    have heq := eq_canonicalExtension_of_continuous hr σ hcont
    intro z
    rw [heq]
    exact tracialTwoNorm_canonicalExtension_le hr _ z

/-- **The designated traces are exactly the traces induced from `T(A)`.**  The
set has not been enlarged: it is the literal range of `canonicalExtension`. -/
theorem designatedTraces_eq_range {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r) :
    designatedTraces hr = Set.range (canonicalExtension (D := D) hr) := by
  ext σ
  constructor
  · intro hσ
    refine ⟨restrictToBase (G D) hr σ, ?_⟩
    refine (eq_canonicalExtension_of_continuous hr σ ?_).symm
    exact (mem_designatedTraces_iff_isCompletionUniformTwoContinuous hr σ).1 hσ
  · rintro ⟨tau, rfl⟩
    intro z
    exact tracialTwoNorm_canonicalExtension_le hr tau z

theorem designatedTraces_nonempty {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r) :
    (designatedTraces hr).Nonempty := by
  obtain ⟨tau⟩ := (inferInstance : Nonempty (TracialState (BaseAlgebra D)))
  exact ⟨canonicalExtension hr tau,
    fun z ↦ tracialTwoNorm_canonicalExtension_le hr tau z⟩

theorem isClosed_designatedTraces {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r) :
    IsClosed (designatedTraces hr) :=
  isClosed_dominatedByGauge _

theorem isCompact_designatedTraces {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r) :
    IsCompact (designatedTraces hr) :=
  isCompact_dominatedByGauge _

theorem isConvexTraceSet_designatedTraces {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r) :
    IsConvexTraceSet (designatedTraces hr) :=
  isConvexTraceSet_dominatedByGauge (fun z ↦ completionGauge_nonneg hr z)

/-- **Factoriality: the designated traces form a face of `T(M)`.**  This is the
conjunct that CCEGSTW Definition 3.13 asks for, and the one the XXII endpoint
was missing. -/
theorem isFaceTraceSet_designatedTraces {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r) :
    IsFaceTraceSet (designatedTraces hr) := by
  refine isFaceTraceSet_dominatedByGauge (fun z ↦ completionGauge_nonneg hr z) ?_
  intro σ C _ hbound z
  have hcont := isCompletionUniformTwoContinuous_of_bounded hr σ hbound
  have heq := eq_canonicalExtension_of_continuous hr σ hcont
  rw [heq]
  exact tracialTwoNorm_canonicalExtension_le hr _ z

/-! ## The negative answer, in the vocabulary of the problem -/

/-- Non-surjectivity of the canonical extension is exactly the failure of the
trace problem in its second form, `X = T(M)`. -/
theorem not_designatedTracesAreAllTraces_of_not_surjective {r : ℕ → ℝ}
    (hr : IsCoordinateNormComparison (G D) r)
    (hns : ¬ Function.Surjective (canonicalExtension (D := D) hr)) :
    ¬ DesignatedTracesAreAllTraces (designatedTraces hr) := by
  intro h
  refine hns fun σ ↦ ?_
  have hmem : σ ∈ designatedTraces hr := by
    rw [h]
    exact Set.mem_univ σ
  rw [designatedTraces_eq_range] at hmem
  exact hmem

/-- The same failure in the first form: some trace on the completion is not
uniform-two continuous. -/
theorem exists_not_isCompletionUniformTwoContinuous_of_not_surjective
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r)
    (hns : ¬ Function.Surjective (canonicalExtension (D := D) hr)) :
    ∃ σ : TracialState (BoundedUniformTwoCompletion (G D) r hr),
      ¬ IsCompletionUniformTwoContinuous (G D) hr σ := by
  by_contra hall
  push_neg at hall
  refine hns fun σ ↦ ?_
  have hmem : σ ∈ designatedTraces hr :=
    (mem_designatedTraces_iff_isCompletionUniformTwoContinuous hr σ).2 (hall σ)
  rw [designatedTraces_eq_range] at hmem
  exact hmem

end

end STW22FactorialCore
end GroupApproximation
