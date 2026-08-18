import GroupApproximation.Analysis.CStarQuotientIdentity
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit

/-!
# The approximate-unit datum, constructed; the C⋆-quotient, unconditional

## What this module does

`CStarQuotientIdentity` proved the quotient C⋆-identity from an
`IdealApproximateUnit` datum -- four norm facts about a filter in the ambient
algebra.  This module constructs the datum for every closed star-stable
two-sided ideal of a C⋆-algebra, and with it assembles the unconditional
conclusion the standing record in `CStarExactness.lean` asks for:

* `idealStarSub I` -- the ideal as a non-unital star subalgebra, so that the
  subtype is a non-unital C⋆-algebra by Mathlib's `SetLike` instances;
* `idealApproximateUnit I` -- Mathlib's increasing approximate unit of that
  C⋆-algebra, pushed forward to the ambient algebra;
* `CStarRing (R ⧸ I)` and `CStarAlgebra (R ⧸ I)` -- the quotient of a
  C⋆-algebra by a closed star-stable two-sided ideal is a C⋆-algebra.

## The one delicate transport, and how it is avoided

The approximate unit lives on the subtype, whose positivity is the *local*
spectral order; the datum's `‖1 - e‖ ≤ 1` is a statement in the ambient
algebra.  The bridge deliberately avoids spectral permanence: a nonnegative
element of the ideal-as-C⋆-algebra is `x * x` for a selfadjoint `x` by the
non-unital continuous-functional-calculus square root, and `star x * x`-form
transports along the inclusion for free, so nonnegativity of the ambient
spectrum comes from `spectrum_star_mul_self_nonneg` in the ambient algebra
rather than from comparing spectra across the inclusion.  The spectral order
is installed as a local instance on the subtype only, inside one section, and
appears in no statement.

## Manuscript status

Infrastructure; certifies no manuscript step on its own.  `SO.16` and
`RE.05` remain **MISSING**; what this closes is item (2) of the standing
record -- the noncommutative C⋆-quotient exists.  With `⊗_min`
(`CStarMinTensorNorm`) beside it, the vocabulary of the textbook definition
of exactness is complete.
-/

namespace GroupApproximation
namespace CStarTensor

open Filter Metric

open scoped Pointwise

universe u

variable {R : Type u} [CStarAlgebra R] (I : Ideal R) [I.IsTwoSided]
  [IsStarStable I]

/-! ## The ideal as a non-unital star subalgebra -/

/-- The ideal, bundled as a non-unital star subalgebra: two-sidedness gives
multiplicative closure, star-stability gives the involution, and the
`ℂ`-scalars act through the algebra map. -/
def idealStarSub : NonUnitalStarSubalgebra ℂ R where
  carrier := I
  add_mem' := fun ha hb => I.add_mem ha hb
  zero_mem' := I.zero_mem
  mul_mem' := fun _ hb => I.mul_mem_left _ hb
  smul_mem' := fun c x hx => by
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ hx
  star_mem' := fun hx => IsStarStable.star_mem hx

omit [I.IsTwoSided] in
@[simp] theorem mem_idealStarSub_iff (x : R) :
    x ∈ idealStarSub I ↔ x ∈ I := Iff.rfl

omit [I.IsTwoSided] in
theorem coe_idealStarSub : ((idealStarSub I : Set R)) = (I : Set R) := rfl

instance [IsClosed (I : Set R)] : IsClosed ((idealStarSub I : Set R)) :=
  inferInstanceAs (IsClosed (I : Set R))

/-! ## Selfadjoint norm bounds from spectral bounds

The ambient-side estimate the datum needs, in the attainment style of
`CStarStateSeparation`: a selfadjoint element whose real spectrum lies in
`[-c, c]` has norm at most `c`. -/

/-- A selfadjoint element's norm is bounded by any bound on the moduli of its
real spectral values: the spectral radius of a selfadjoint element is its
norm and is attained at a real spectral value. -/
theorem norm_le_of_isSelfAdjoint_of_spectrum_bounded [Nontrivial R] {y : R}
    (hy : IsSelfAdjoint y) {c : ℝ}
    (hb : ∀ s ∈ spectrum ℝ y, |s| ≤ c) : ‖y‖ ≤ c := by
  obtain ⟨z, hz, hznorm⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty
      (spectrum.nonempty y)
  have := hy.spectralRadius_eq_nnnorm
  rw [this] at hznorm
  have hzy : ‖z‖ = ‖y‖ := by
    have h : ‖z‖₊ = ‖y‖₊ := by exact_mod_cast hznorm
    exact congrArg NNReal.toReal h
  have hzre : z = z.re := hy.mem_spectrum_eq_re hz
  have hre_mem : z.re ∈ spectrum ℝ y := by
    apply spectrum.of_algebraMap_mem ℂ
    show ((z.re : ℝ) : ℂ) ∈ spectrum ℂ y
    rw [← hzre]
    exact hz
  have habs : ‖z‖ = |z.re| := by
    conv_lhs => rw [hzre]
    exact Complex.norm_real z.re
  rw [← hzy, habs]
  exact hb z.re hre_mem

/-! ## The datum -/

section Construction

variable [IsClosed (I : Set R)] [Nontrivial R]

noncomputable local instance instIdealOrder :
    PartialOrder ↥(idealStarSub I) :=
  CStarAlgebra.spectralOrder _

noncomputable local instance instIdealStarOrdered :
    StarOrderedRing ↥(idealStarSub I) :=
  CStarAlgebra.spectralOrderedRing _

/-- **The approximate-unit datum of a closed star-stable two-sided ideal**:
Mathlib's increasing approximate unit of the ideal viewed as a non-unital
C⋆-algebra, pushed forward along the inclusion. -/
noncomputable def idealApproximateUnit : IdealApproximateUnit I where
  filter := Filter.map Subtype.val
    (CStarAlgebra.approximateUnit ↥(idealStarSub I))
  neBot := by
    haveI : (CStarAlgebra.approximateUnit ↥(idealStarSub I)).NeBot :=
      inferInstance
    exact Filter.map_neBot
  eventually_mem := by
    rw [Filter.eventually_map]
    exact Filter.Eventually.of_forall fun e => e.2
  eventually_isSelfAdjoint := by
    rw [Filter.eventually_map]
    filter_upwards
      [(CStarAlgebra.increasingApproximateUnit
        ↥(idealStarSub I)).eventually_isSelfAdjoint] with e he
    simpa [IsSelfAdjoint] using congrArg Subtype.val he
  eventually_norm_one_sub := by
    rw [Filter.eventually_map]
    filter_upwards
      [(CStarAlgebra.increasingApproximateUnit
          ↥(idealStarSub I)).eventually_nonneg,
        (CStarAlgebra.increasingApproximateUnit
          ↥(idealStarSub I)).eventually_norm] with e he0 he1
    -- `e` is a square of a selfadjoint element of the ideal.
    have hsa : IsSelfAdjoint e := by
      have h := he0
      exact IsSelfAdjoint.of_nonneg h
    have hqs : QuasispectrumRestricts e ContinuousMap.realToNNReal := by
      have h := he0
      obtain ⟨-, hq⟩ := h
      simpa using hq
    obtain ⟨x, hx, -, hxx⟩ :=
      CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hsa hqs
    -- Transport `e = star x * x` to the ambient algebra.
    have hcoe : (e : R) = star (x : R) * (x : R) := by
      have h1 : ((x * x : ↥(idealStarSub I)) : R) = (x : R) * (x : R) := rfl
      have h2 : star (x : R) = ((x : R)) := by
        simpa [IsSelfAdjoint] using congrArg Subtype.val hx
      rw [← hxx] at *
      rw [h1, h2]
    -- Ambient spectrum of `e` is nonnegative and bounded by `1`.
    have hspec0 : ∀ s ∈ spectrum ℝ (e : R), 0 ≤ s := by
      rw [hcoe]
      exact spectrum_star_mul_self_nonneg
    have henorm : ‖(e : R)‖ ≤ 1 := he1
    have hspec1 : ∀ s ∈ spectrum ℝ (e : R), s ≤ 1 := by
      intro s hs
      have : ((s : ℝ) : ℂ) ∈ spectrum ℂ (e : R) :=
        spectrum.algebraMap_mem ℂ hs
      have hn := spectrum.norm_le_norm_of_mem this
      rw [Complex.norm_real, Real.norm_eq_abs] at hn
      calc s ≤ |s| := le_abs_self s
        _ ≤ ‖(e : R)‖ := hn
        _ ≤ 1 := henorm
    -- Hence `1 - e` is selfadjoint with spectrum in `[0, 1]`.
    have hesa : IsSelfAdjoint (e : R) := by
      rw [hcoe]
      exact IsSelfAdjoint.star_mul_self _
    have h1sa : IsSelfAdjoint ((1 : R) - (e : R)) :=
      (IsSelfAdjoint.one R).sub hesa
    refine norm_le_of_isSelfAdjoint_of_spectrum_bounded h1sa fun s hs => ?_
    -- Spectral mapping for `1 - e`.
    have hshift : spectrum ℝ ((1 : R) - (e : R))
        = ({(1 : ℝ)} : Set ℝ) - spectrum ℝ (e : R) := by
      have h := spectrum.singleton_sub_eq (R := ℝ) ((e : R)) 1
      rw [map_one] at h
      exact h.symm
    rw [hshift] at hs
    obtain ⟨u, hu, v, hv, huv⟩ := hs
    rw [Set.mem_singleton_iff] at hu
    subst hu
    have h0v : 0 ≤ v := hspec0 v hv
    have h1v : v ≤ 1 := hspec1 v hv
    have : (1 : ℝ) - v = s := huv
    rw [← this, abs_le]
    constructor <;> linarith
  tendsto_mul_right := by
    intro j hj
    rw [Filter.tendsto_map'_iff]
    set jI : ↥(idealStarSub I) := ⟨j, hj⟩ with hjI
    have h := (CStarAlgebra.increasingApproximateUnit
      ↥(idealStarSub I)).tendsto_mul_left jI
    have h0 : Tendsto (fun e => ‖jI * e - jI‖)
        (CStarAlgebra.approximateUnit ↥(idealStarSub I)) (nhds 0) := by
      rw [← tendsto_iff_norm_sub_tendsto_zero]
      exact h
    have hshape : (fun e : ↥(idealStarSub I) => ‖j - j * (e : R)‖)
        = fun e => ‖jI * e - jI‖ := by
      funext e
      have hc : ((jI * e : ↥(idealStarSub I)) : R) = j * (e : R) := rfl
      rw [show ‖jI * e - jI‖ = ‖((jI * e : ↥(idealStarSub I)) : R) - j‖
          from rfl, hc, norm_sub_rev]
    show Tendsto ((fun e : ↥(idealStarSub I) => ‖j - j * (e : R)‖))
      (CStarAlgebra.approximateUnit ↥(idealStarSub I)) (nhds 0)
    rw [hshape]
    exact h0

end Construction

/-! ## The unconditional C⋆-quotient -/

section Quotient

variable [IsClosed (I : Set R)] [Nontrivial R]

/-- **The quotient of a C⋆-algebra by a closed star-stable two-sided ideal
satisfies the C⋆-identity**, unconditionally: the approximate-unit datum is
constructed rather than assumed. -/
noncomputable instance (priority := 100) instCStarRingQuotient :
    CStarRing (R ⧸ I) :=
  isCStarRing_quotient (idealApproximateUnit I)

/-- The involution respects the scalars on the quotient. -/
instance instStarModuleQuotient : StarModule ℂ (R ⧸ I) where
  star_smul c x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← quotient_mk_smul I c a, quotient_star_mk, quotient_star_mk,
      star_smul, quotient_mk_smul]

/-- **The quotient of a C⋆-algebra by a closed star-stable two-sided ideal is
a C⋆-algebra.**  Every field was supplied piecewise: the noncommutative
normed ring and algebra by `CStarIdealQuotient`, the ⋆-ring by
`CStarSeminormQuotient`, completeness by Mathlib, and the C⋆-identity by the
approximate unit above. -/
noncomputable instance instCStarAlgebraQuotient : CStarAlgebra (R ⧸ I) where

end Quotient

end CStarTensor
end GroupApproximation
