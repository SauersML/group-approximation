import GroupApproximation.Analysis.PolarLiftingGeneralCStar
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# (V3) Correcting an almost-isometry into an isometry, without moving its range

Voiculescu's one-step approximation produces its isometry in two stages.  Glimm's
lemma, applied to the matrix amplification of `A`, supplies a *frame* — a linear
map `T : K → H` whose Gram operator `T⋆T` is close to `1` and whose range avoids
a prescribed finite-dimensional subspace — and the frame is then corrected to a
genuine isometry.  This module is the correction, and it is unconditional: it
uses neither Glimm's lemma nor the amplification, only the continuous functional
calculus.

## What the correction has to preserve

Two things, and the second is the reason the correction is a right multiplier
rather than an arbitrary nearby isometry.

*The compression.*  `T⋆ a T` is what the amplification controls, and the
isometry has to control it too; `norm_sub_compress_le` below is the exchange, and
its constant degrades only by the Gram defect.

*The escape.*  The frame's range misses the obstruction subspace, and the
corrected isometry has to miss it as well.  Correcting on the right — `W = T ∘ c`
with `c` acting on the source — makes that automatic, because the range can only
shrink (`comp_mem_of_mem`).  A correction on the left, or a nearby isometry
produced by an abstract argument, would have to re-prove the escape.

## The correction is already in the tree

`Analysis/PolarLiftingGeneralCStar` carries the polar correction
`x ↦ x(x⋆x)^{-1/2}` for a single unital C⋆-algebra, with the two facts this
module needs: `polarInvSqrt_gram_polarInvSqrt`, that `(x⋆x)^{-1/2}` conjugates
`x⋆x` to `1`, and `norm_polarInvSqrt_sub_one_le`, that it sits within twice the
Gram defect of `1`.  Both are stated about `star x * x` for an element `x` of the
algebra, and here the Gram operator `T⋆T` is *not* of that shape, because `T`
runs between two different spaces and so is not an element of any one algebra.

The bridge is that `T⋆T` is nonetheless a nonnegative element of `B(K)`, so it
*is* `star x * x` for `x = (T⋆T)^{1/2}` in that algebra — the factorisation
`Analysis/CStarMatrixFactorization.exists_star_mul_self_of_nonneg` performs at
the abstract level.  Nonnegativity is read off the spectrum rather than off the
inner product: a self-adjoint element within `1/2` of `1` has spectrum in
`[1/2, 3/2]`, which is `gram_nonneg` below.  So no estimate is reproved here.

## The hypothesis is not vacuous

`repair_subsingleton_of_zero` is the model test: at `T = 0` the conclusion forces
`(1 : K →L[ℂ] K) = 0`, hence `K = 0`.  The Gram hypothesis therefore cannot be
met by the zero map on a nonzero source, which is the degeneracy that would make
the statement carry no content.
-/

namespace GroupApproximation
namespace ShulmanFill

noncomputable section

variable {K H : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ## The Gram operator -/

/-- The Gram operator of a map between Hilbert spaces is self-adjoint. -/
theorem isSelfAdjoint_gram (T : K →L[ℂ] H) :
    IsSelfAdjoint (ContinuousLinearMap.adjoint T ∘L T) := by
  have h : star (ContinuousLinearMap.adjoint T ∘L T)
      = ContinuousLinearMap.adjoint T ∘L T := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  exact h

/-- **A self-adjoint operator within `1/2` of the identity is nonnegative.**  Its
real spectrum lies in `[1/2, 3/2]`, and for a self-adjoint element that is the
whole of nonnegativity.  Reading positivity off the spectrum rather than off the
inner product is what lets the polar correction of
`Analysis/PolarLiftingGeneralCStar` be reached: that correction is stated about
`star x * x`, and the factorisation of a nonnegative element supplies the `x`. -/
theorem gram_nonneg {b : K →L[ℂ] K} (hsa : IsSelfAdjoint b)
    (h : ‖b - 1‖ ≤ 1 / 2) : 0 ≤ b := by
  rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) b hsa]
  intro t ht
  have habs : |t - 1| ≤ ‖b - 1‖ :=
    PolarLiftingGeneralCStar.abs_sub_one_le_of_mem_spectrum ht
  have hlow := neg_le_of_abs_le (habs.trans h)
  linarith

/-! ## The correcting multiplier -/

/-- **The correction exists.**  A self-adjoint operator `b` within `1/2` of `1`
has a self-adjoint `c` with `c b c = 1` and `‖c - 1‖ ≤ 2‖b - 1‖`: the inverse
square root of `b`, reached through the polar correction of
`Analysis/PolarLiftingGeneralCStar` at the square root of `b`. -/
theorem exists_gramCorrection {b : K →L[ℂ] K} (hsa : IsSelfAdjoint b)
    (h : ‖b - 1‖ ≤ 1 / 2) :
    ∃ c : K →L[ℂ] K, IsSelfAdjoint c ∧ ‖c - 1‖ ≤ 2 * ‖b - 1‖ ∧ c * b * c = 1 := by
  have hb : 0 ≤ b := gram_nonneg hsa h
  have hxx : star (CFC.sqrt b) * CFC.sqrt b = b := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg b)).star_eq,
      CFC.sqrt_mul_sqrt_self b hb]
  have hx : ‖star (CFC.sqrt b) * CFC.sqrt b - 1‖ ≤ 1 / 2 := by rw [hxx]; exact h
  refine ⟨PolarLiftingGeneralCStar.polarInvSqrt (CFC.sqrt b),
    PolarLiftingGeneralCStar.polarInvSqrt_isSelfAdjoint _, ?_, ?_⟩
  · have hnorm := PolarLiftingGeneralCStar.norm_polarInvSqrt_sub_one_le hx
    rwa [hxx] at hnorm
  · have hgram := PolarLiftingGeneralCStar.polarInvSqrt_gram_polarInvSqrt hx
    rwa [hxx] at hgram

/-! ## Conjugating by the correction -/

/-- The adjoint of a self-adjoint operator is itself. -/
theorem adjoint_eq_self {c : K →L[ℂ] K} (hc : IsSelfAdjoint c) :
    ContinuousLinearMap.adjoint c = c :=
  (ContinuousLinearMap.star_eq_adjoint c).symm.trans hc.star_eq

/-- Compressing along a right-corrected map conjugates the original
compression. -/
theorem adjoint_comp_conj (T : K →L[ℂ] H) {c : K →L[ℂ] K} (hc : IsSelfAdjoint c)
    (y : H →L[ℂ] H) :
    ContinuousLinearMap.adjoint (T ∘L c) ∘L y ∘L (T ∘L c)
      = c * (ContinuousLinearMap.adjoint T ∘L y ∘L T) * c := by
  have hca := adjoint_eq_self hc
  ext x
  simp [ContinuousLinearMap.adjoint_comp, hca, ContinuousLinearMap.mul_def]

/-- The Gram operator of a right-corrected map is the conjugated Gram
operator. -/
theorem adjoint_comp_self_conj (T : K →L[ℂ] H) {c : K →L[ℂ] K}
    (hc : IsSelfAdjoint c) :
    ContinuousLinearMap.adjoint (T ∘L c) ∘L (T ∘L c)
      = c * (ContinuousLinearMap.adjoint T ∘L T) * c := by
  have hca := adjoint_eq_self hc
  ext x
  simp [ContinuousLinearMap.adjoint_comp, hca, ContinuousLinearMap.mul_def]

/-- **The conjugation estimate**, in any normed ring: conjugating by an element
near `1` moves an element by at most its norm times the defect, twice over.  The
identity behind it is `c z c - z = (c-1)z(c-1) + (c-1)z + z(c-1)`. -/
theorem norm_conj_sub_le {A : Type*} [NormedRing A] (c z : A) :
    ‖c * z * c - z‖ ≤ ‖z‖ * ‖c - 1‖ * (‖c - 1‖ + 2) := by
  have hid : c * z * c - z
      = (c - 1) * z * (c - 1) + (c - 1) * z + z * (c - 1) := by noncomm_ring
  have h1 : ‖(c - 1) * z * (c - 1)‖ ≤ ‖c - 1‖ * ‖z‖ * ‖c - 1‖ :=
    (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
  have h2 : ‖(c - 1) * z‖ ≤ ‖c - 1‖ * ‖z‖ := norm_mul_le _ _
  have h3 : ‖z * (c - 1)‖ ≤ ‖z‖ * ‖c - 1‖ := norm_mul_le _ _
  calc ‖c * z * c - z‖
      = ‖(c - 1) * z * (c - 1) + (c - 1) * z + z * (c - 1)‖ := by rw [hid]
    _ ≤ ‖(c - 1) * z * (c - 1) + (c - 1) * z‖ + ‖z * (c - 1)‖ := norm_add_le _ _
    _ ≤ ‖(c - 1) * z * (c - 1)‖ + ‖(c - 1) * z‖ + ‖z * (c - 1)‖ :=
        add_le_add (norm_add_le ((c - 1) * z * (c - 1)) ((c - 1) * z)) le_rfl
    _ ≤ ‖c - 1‖ * ‖z‖ * ‖c - 1‖ + ‖c - 1‖ * ‖z‖ + ‖z‖ * ‖c - 1‖ := by
        exact add_le_add (add_le_add h1 h2) h3
    _ = ‖z‖ * ‖c - 1‖ * (‖c - 1‖ + 2) := by ring

/-! ## The repair -/

/-- **(V3b) The correction of an almost-isometry.**  A map whose Gram operator is
within `1/2` of the identity is a right multiple of a genuine isometry with the
same range constraint, and the isometry's compressions differ from the original's
by a factor governed only by the Gram defect.

The correction is `W = T ∘ c`; the fourth clause is stated at every `y ∈ B(H)`
because the consumer applies it to a finite set of operators at once. -/
theorem exists_isometry_of_norm_gram_le (T : K →L[ℂ] H)
    (h : ‖ContinuousLinearMap.adjoint T ∘L T - 1‖ ≤ 1 / 2) :
    ∃ c : K →L[ℂ] K, IsSelfAdjoint c ∧
      ‖c - 1‖ ≤ 2 * ‖ContinuousLinearMap.adjoint T ∘L T - 1‖ ∧
      ContinuousLinearMap.adjoint (T ∘L c) ∘L (T ∘L c) = 1 ∧
      ∀ y : H →L[ℂ] H,
        ‖ContinuousLinearMap.adjoint (T ∘L c) ∘L y ∘L (T ∘L c)
            - ContinuousLinearMap.adjoint T ∘L y ∘L T‖
          ≤ ‖ContinuousLinearMap.adjoint T ∘L y ∘L T‖ * ‖c - 1‖ * (‖c - 1‖ + 2) := by
  obtain ⟨c, hc, hcnorm, hcgram⟩ :=
    exists_gramCorrection (isSelfAdjoint_gram T) h
  refine ⟨c, hc, hcnorm, ?_, ?_⟩
  · rw [adjoint_comp_self_conj T hc]
    exact hcgram
  · intro y
    rw [adjoint_comp_conj T hc y]
    exact norm_conj_sub_le c (ContinuousLinearMap.adjoint T ∘L y ∘L T)

omit [CompleteSpace K] [CompleteSpace H] in
/-- **The escape survives the correction.**  Correcting on the right can only
shrink the range, so a frame avoiding an obstruction subspace stays inside it
after the correction.  This is the clause a nearby-isometry argument would have
to re-prove. -/
theorem comp_mem_of_mem (T : K →L[ℂ] H) (c : K →L[ℂ] K) (V : Submodule ℂ H)
    (hT : ∀ x, T x ∈ V) (x : K) : (T ∘L c) x ∈ V :=
  hT (c x)

/-! ## The model test -/

/-- **The hypothesis is not vacuous.**  At `T = 0` the repaired Gram operator is
`0`, so the conclusion asserts `(1 : K →L[ℂ] K) = 0`, which happens only on the
zero space.  So no nonzero source space admits the zero frame, and the statement
above is not satisfied by a degenerate witness. -/
theorem repair_subsingleton_of_zero
    (h : ‖ContinuousLinearMap.adjoint (0 : K →L[ℂ] H) ∘L (0 : K →L[ℂ] H) - 1‖
      ≤ 1 / 2) : Subsingleton K := by
  obtain ⟨c, _, _, hiso, _⟩ := exists_isometry_of_norm_gram_le (0 : K →L[ℂ] H) h
  have hzero : ((0 : K →L[ℂ] H) ∘L c) = 0 := ContinuousLinearMap.zero_comp c
  rw [hzero, map_zero, ContinuousLinearMap.zero_comp] at hiso
  refine ⟨fun a b ↦ ?_⟩
  have ha : a = 0 := by
    have := congrArg (fun S : K →L[ℂ] K ↦ S a) hiso
    simpa using this.symm
  have hb : b = 0 := by
    have := congrArg (fun S : K →L[ℂ] K ↦ S b) hiso
    simpa using this.symm
  rw [ha, hb]

end

end ShulmanFill
end GroupApproximation
