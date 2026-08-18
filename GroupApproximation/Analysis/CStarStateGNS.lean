import GroupApproximation.Analysis.CStarStateSeparation
import GroupApproximation.Analysis.CStarTensorProductConcrete
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.Complex.Order

/-!
# The GNS representations of states, as a jointly isometric family

## What this module provides

`CStarStateSeparation` produced norm-attaining states: unital contractions
`f : A →L[ℂ] ℂ` with `f (star a * a) = ‖a‖²`.  This module turns each state
into a ⋆-representation on a Hilbert space -- Mathlib's GNS construction --
and proves the two facts the canonical minimal tensor norm needs from the
family:

* **contractivity**: `‖gnsRep φ a‖ ≤ ‖a‖` for every state `φ`
  (`State.norm_gnsRep_apply_le`);
* **joint isometry**: for every `a` some state `φ` has
  `‖a‖ ≤ ‖gnsRep φ a‖`, witnessed by the cyclic vector of a norm-attaining
  state (`exists_state_norm_le_gnsRep`); hence the family separates points
  (`eq_zero_of_forall_state_inner_eq_zero`).

With these, a supremum of spatial seminorms over pairs of states is a
*C⋆-norm* whose restriction to each factor is the original norm -- the
canonical, set-indexed substitute for "all representations" that Stage C of
the tensor-lane roadmap (`CStarTensorProduct.lean`) calls for.

## How the order dependence is contained

Mathlib's GNS construction consumes a `PositiveLinearMap` and therefore a
`[PartialOrder A]` and `[StarOrderedRing A]`.  The concrete algebras of this
repository do not carry order instances, and the public statements here do
not mention any.  Inside this module the canonical spectral order
(`CStarAlgebra.spectralOrder`, which its own docstring offers for exactly
this use) is installed as a *local* instance, specialised to the variable
`A` so that it cannot leak onto `ℂ` or any other algebra; the state's
positivity in that order is derived from the order-free Kadison lemmas of
`CStarStateSeparation` through `StarOrderedRing.le_iff` and closure
induction.  Every exported declaration bakes the order into its term, so
consumers see only: a state, a Hilbert space, a `StarRep`, and norms.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `SO.16` and
`RE.05` remain **MISSING**.  This is Stage C.2 of the tensor-lane roadmap:
the state-indexed representation family.  The supremum norm over state pairs
and the `⊗_min` object are the next layer, not here.
-/

namespace GroupApproximation
namespace CStarState

open scoped ComplexOrder InnerProductSpace

universe u

/-! ## States, bundled -/

/-- A **state** on a unital C⋆-algebra, in the order-free spelling of this
development: a unital contraction.  By `CStarStateSeparation` such a
functional is automatically positive (real on selfadjoint elements,
nonnegative on `star x * x`), which is Kadison's characterization; bundling
the unital-contraction side keeps the definition free of order instances. -/
structure State (A : Type u) [CStarAlgebra A] where
  /-- The underlying continuous linear functional. -/
  toCLM : A →L[ℂ] ℂ
  /-- A state is unital. -/
  map_one : toCLM 1 = 1
  /-- A state is a contraction. -/
  norm_le : ‖toCLM‖ ≤ 1

variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

/-- The norm-attaining state, repackaged from
`CStarStateSeparation.exists_state_star_mul_self`. -/
theorem State.exists_star_mul_self (a : A) :
    ∃ φ : State A, φ.toCLM (star a * a) = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
  obtain ⟨f, h1, hle, hval⟩ := exists_state_star_mul_self a
  exact ⟨⟨f, h1, hle⟩, hval⟩

/-- States are positive on elements of the form `star x * x`, with real
value: the order-free Kadison positivity, restated on the bundle. -/
theorem State.star_mul_self_nonneg (φ : State A) (x : A) :
    0 ≤ (φ.toCLM (star x * x)).re ∧ (φ.toCLM (star x * x)).im = 0 :=
  state_apply_star_mul_self_nonneg φ.toCLM φ.map_one φ.norm_le x

/-! ## The spectral-order bridge and the GNS space

Everything in this section mentions the spectral order; nothing outside it
does. -/

section SpectralBridge

noncomputable local instance (priority := 0) instSpectralOrder :
    PartialOrder A :=
  CStarAlgebra.spectralOrder A

noncomputable local instance (priority := 0) instSpectralStarOrdered :
    StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-- A state, as a positive linear functional for the spectral order.  The
monotonicity is exactly the Kadison positivity of
`CStarStateSeparation`, transported through `StarOrderedRing.le_iff` and
closure induction. -/
noncomputable def State.toPositive (φ : State A) : A →ₚ[ℂ] ℂ :=
  { φ.toCLM.toLinearMap with
    monotone' := by
      intro x y hxy
      rw [StarOrderedRing.le_iff] at hxy
      obtain ⟨p, hp, rfl⟩ := hxy
      have hp0 : (0 : ℂ) ≤ φ.toCLM p := by
        induction hp using AddSubmonoid.closure_induction with
        | mem s hs =>
            obtain ⟨w, rfl⟩ := hs
            have h := φ.star_mul_self_nonneg w
            rw [Complex.le_def]
            exact ⟨by simpa using h.1, by simpa using h.2.symm⟩
        | one => simp
        | mul c d hc hd hc0 hd0 =>
            rw [map_add]
            exact add_nonneg hc0 hd0
      show φ.toCLM x ≤ φ.toCLM (x + p)
      rw [map_add]
      exact le_add_of_nonneg_right hp0 }

@[simp] theorem State.toPositive_apply (φ : State A) (x : A) :
    φ.toPositive x = φ.toCLM x := rfl

/-- The GNS Hilbert space of a state: Mathlib's GNS completion of the
positive functional the state induces for the spectral order.  The order is
baked into this definition; consumers never see it. -/
noncomputable def State.GNSSpace (φ : State A) : Type u :=
  φ.toPositive.GNS

noncomputable instance State.instNormedAddCommGroupGNSSpace (φ : State A) :
    NormedAddCommGroup φ.GNSSpace :=
  inferInstanceAs (NormedAddCommGroup φ.toPositive.GNS)

noncomputable instance State.instInnerProductSpaceGNSSpace (φ : State A) :
    InnerProductSpace ℂ φ.GNSSpace :=
  inferInstanceAs (InnerProductSpace ℂ φ.toPositive.GNS)

instance State.instCompleteSpaceGNSSpace (φ : State A) :
    CompleteSpace φ.GNSSpace :=
  inferInstanceAs (CompleteSpace φ.toPositive.GNS)

/-- The GNS ⋆-representation of a state, in the `StarRep` format of the
tensor lane. -/
noncomputable def State.gnsRep (φ : State A) :
    CStarTensor.StarRep A φ.GNSSpace :=
  CStarTensor.StarRep.ofStarAlgHom
    (H := φ.GNSSpace) φ.toPositive.gnsStarAlgHom

/-- The cyclic vector: the class of `1` in the GNS space. -/
noncomputable def State.gnsVector (φ : State A) : φ.GNSSpace :=
  ((φ.toPositive.toPreGNS 1 : φ.toPositive.PreGNS) : φ.toPositive.GNS)

/-- Operators of the completion are bounded by the operator norm of the
underlying map; recorded here because the pinned Mathlib has the statement
only for `NormedAddGroupHom`. -/
private theorem norm_completion_apply_le {E F : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] (f : E →L[ℂ] F)
    (x : UniformSpace.Completion E) :
    ‖f.completion x‖ ≤ ‖f‖ * ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      apply isClosed_le
      · exact continuous_norm.comp f.completion.continuous
      · exact continuous_const.mul continuous_norm
  | ih x =>
      rw [ContinuousLinearMap.completion_apply_coe,
        UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
      exact f.le_opNorm x

/-- **The GNS representation of a state is contractive.** -/
theorem State.norm_gnsRep_apply_le (φ : State A) (a : A) :
    ‖(φ.gnsRep).hom a‖ ≤ ‖a‖ := by
  have hle : ∀ x : φ.GNSSpace, ‖(φ.gnsRep).hom a x‖ ≤ ‖a‖ * ‖x‖ := by
    intro x
    show ‖(φ.toPositive.leftMulMapPreGNS a).completion x‖ ≤ ‖a‖ * ‖x‖
    have h1 : ‖φ.toPositive.leftMulMapPreGNS a‖ ≤ ‖a‖ :=
      LinearMap.mkContinuous_norm_le _ (norm_nonneg a) _
    calc ‖(φ.toPositive.leftMulMapPreGNS a).completion x‖
        ≤ ‖φ.toPositive.leftMulMapPreGNS a‖ * ‖x‖ :=
          norm_completion_apply_le _ x
      _ ≤ ‖a‖ * ‖x‖ := by gcongr
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) hle

/-- The cyclic vector is a unit vector: its norm squares to `φ 1 = 1`. -/
theorem State.norm_gnsVector (φ : State A) : ‖φ.gnsVector‖ = 1 := by
  show ‖((φ.toPositive.toPreGNS 1 : φ.toPositive.PreGNS) :
      φ.toPositive.GNS)‖ = 1
  rw [UniformSpace.Completion.norm_coe, PositiveLinearMap.preGNS_norm_def]
  simp

/-- **The matrix coefficient of the cyclic vector computes the state**:
`‖gnsRep φ a Ω‖² = (φ (star a * a)).re`. -/
theorem State.normSq_gnsRep_apply_gnsVector (φ : State A) (a : A) :
    ‖(φ.gnsRep).hom a φ.gnsVector‖ ^ 2 = (φ.toCLM (star a * a)).re := by
  have h1 : (φ.gnsRep).hom a φ.gnsVector
      = ((φ.toPositive.toPreGNS a : φ.toPositive.PreGNS) :
          φ.toPositive.GNS) := by
    show (φ.toPositive.leftMulMapPreGNS a).completion
        ((φ.toPositive.toPreGNS 1 : φ.toPositive.PreGNS) :
          φ.toPositive.GNS) = _
    rw [ContinuousLinearMap.completion_apply_coe]
    congr 1
    simp
  rw [h1, UniformSpace.Completion.norm_coe]
  have h2 := PositiveLinearMap.preGNS_norm_sq (f := φ.toPositive)
    (φ.toPositive.toPreGNS a)
  rw [PositiveLinearMap.ofPreGNS_toPreGNS] at h2
  have h3 := congrArg Complex.re h2
  rw [Complex.ofReal_re] at h3
  rw [h3]
  rfl

end SpectralBridge

/-! ## The joint isometry and separation -/

/-- **The family of GNS representations attains every norm**: for each `a`
the norm-attaining state's representation satisfies `‖a‖ ≤ ‖gnsRep φ a‖`.
With contractivity this makes the family jointly isometric. -/
theorem exists_state_norm_le_gnsRep (a : A) :
    ∃ φ : State A, ‖a‖ ≤ ‖(φ.gnsRep).hom a‖ := by
  obtain ⟨φ, hφ⟩ := State.exists_star_mul_self a
  refine ⟨φ, ?_⟩
  have h1 : ‖(φ.gnsRep).hom a φ.gnsVector‖ ^ 2 = ‖a‖ ^ 2 := by
    rw [State.normSq_gnsRep_apply_gnsVector, hφ]
    push_cast
    simp
  have h2 : ‖(φ.gnsRep).hom a φ.gnsVector‖
      ≤ ‖(φ.gnsRep).hom a‖ * ‖φ.gnsVector‖ :=
    ContinuousLinearMap.le_opNorm _ _
  rw [State.norm_gnsVector, mul_one] at h2
  nlinarith [norm_nonneg ((φ.gnsRep).hom a φ.gnsVector),
    norm_nonneg ((φ.gnsRep).hom a), norm_nonneg a]

/-- **The GNS family separates points**: an element all of whose matrix
coefficients vanish, over every state, is zero.  This is the
family-quantified form of the vector-functional separation that the spatial
lane's injectivity argument consumes for a single faithful pair. -/
theorem eq_zero_of_forall_state_inner_eq_zero (a : A)
    (h : ∀ (φ : State A) (ξ η : φ.GNSSpace),
      ⟪η, (φ.gnsRep).hom a ξ⟫_ℂ = 0) :
    a = 0 := by
  obtain ⟨φ, hφ⟩ := exists_state_norm_le_gnsRep a
  have hT : (φ.gnsRep).hom a = 0 := by
    ext ξ
    have h0 := h φ ξ ((φ.gnsRep).hom a ξ)
    rw [inner_self_eq_zero] at h0
    simpa using h0
  rw [hT] at hφ
  simp only [norm_zero] at hφ
  exact norm_le_zero_iff.mp hφ

end CStarState
end GroupApproximation
