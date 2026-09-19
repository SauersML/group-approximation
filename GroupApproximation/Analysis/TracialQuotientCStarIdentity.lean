import GroupApproximation.Analysis.HilbertSchmidtApproximateUnit
import GroupApproximation.Analysis.TracialMatrixUltraproduct

/-!
# The C-star identity for the tracial matrix quotient, proved a second way

`Analysis/TracialQuotientCStar.lean` is the canonical home of the quotient's
C-star structure: it installs the `CStarRing` and `CStarAlgebra` instances
and records the exact quotient-norm formula
`‖a + J‖ = inf { ‖a - a e‖ : e ∈ J }`, consuming the identity proved
here.  This file is the proof of the identity's hard direction, together
with the reusable sequence-level cut API it runs on:

* `cutSeq`: the coordinatewise spectral cut of a bounded sequence, an
  orthogonal projection in every coordinate, uniformly bounded by `1`;
* `isHilbertSchmidtNull_cutSeq`: the cut of an ideal element stays in the
  ideal — clause 2 of the approximate unit, with the threshold fixed before
  the filter moves;
* `norm_sub_mul_cutSeq_le`: the cut moves its sequence by at most the square
  root of the threshold, uniformly — clause 1;
* `norm_sq_le_norm_star_mul_self`: **the C-star identity**, hard direction,
  for the quotient norm at an arbitrary filter.

The instances themselves are declared once, downstream in
`Analysis/TracialQuotientCStar.lean`, which imports this module; declaring
them a second time here would put two defeq-but-distinct `CStarAlgebra`
structures on the same type in every downstream file.

## The three-line estimate, honestly three lines

For a class `x` with representative `b`, a fresh representative `r` of
`x⋆ x` with `‖r‖ < ‖x⋆ x‖ + δ`, and `k := r - b⋆ b` (an ideal element), let
`e` be the coordinatewise cut of `k` at threshold `δ²`.  Then `b e` is in the
ideal, so `‖x‖ ≤ ‖b - b e‖`; and in every coordinate

```text
‖bₙ(1-eₙ)‖² = ‖(1-eₙ)(bₙ⋆bₙ)(1-eₙ)‖
            ≤ ‖(1-eₙ) rₙ (1-eₙ)‖ + ‖(1-eₙ) kₙ (1-eₙ)‖
            ≤ ‖r‖ + δ  <  ‖x⋆ x‖ + 2δ,
```

using `‖1-eₙ‖ ≤ 1` (a projection complement) and clause 1 on the middle
term.  Taking suprema, `‖x‖² ≤ ‖x⋆ x‖ + 2δ` for every `δ > 0`.

## Instance discipline

The `CStarRing` instance (in the canonical file) is a **mixin over the
existing structure**: the `NormedRing`, `StarRing`, `NormedAlgebra` and
`CompleteSpace` instances are the ones `TracialMatrixUltraproduct`
hand-built, and the `CStarAlgebra` bundle is assembled from those same
canonical parts.  A fresh `CStarAlgebra` carrying its own norm would fork
`‖·‖` on the quotient and silently detach every existing lemma from the
instance the lift sees.
-/

namespace GroupApproximation
namespace TracialUltraproduct

open Filter Matrix HilbertSchmidtApproximateUnit KazhdanCornerMatrices
  ExactInvolutionLifts
open scoped Matrix.Norms.L2Operator

set_option synthInstance.maxHeartbeats 2000000
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

noncomputable section

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (l : Filter ℕ)

/-! ## The sequence-level approximate unit -/

/-- The coordinatewise spectral cut of a bounded sequence: an orthogonal
projection in every coordinate, hence uniformly bounded by `1`. -/
def cutSeq (k : ModelBoundedSequence X) (t : ℝ) : ModelBoundedSequence X :=
  ⟨fun n ↦ cut (X n) (k n) t, memℓp_infty ⟨1, by
    rintro _ ⟨n, rfl⟩
    exact norm_cut_le_one (X n) (k n) t⟩⟩

@[simp] theorem cutSeq_apply (k : ModelBoundedSequence X) (t : ℝ) (n : ℕ) :
    cutSeq X k t n = cut (X n) (k n) t := rfl

/-- **Clause 2, sequence level.**  The cut of an ideal element stays in the
ideal: the threshold is fixed before the filter moves, so
`t·‖eₙ‖₂² ≤ ‖kₙ‖₂²` sends the cut to zero wherever `k` goes to zero. -/
theorem isHilbertSchmidtNull_cutSeq {k : ModelBoundedSequence X}
    (hk : IsHilbertSchmidtNull X l k) {t : ℝ} (ht : 0 < t) :
    IsHilbertSchmidtNull X l (cutSeq X k t) := by
  rw [isHilbertSchmidtNull_iff_sq] at hk ⊢
  have hb : ∀ n, hsNormSq (X n) (cutSeq X k t n)
      ≤ hsNormSq (X n) (k n) / t := by
    intro n
    have h := hsNormSq_cut_le (X n) (k n) t Fintype.card_pos
    rw [le_div_iff₀ ht]
    calc hsNormSq (X n) (cutSeq X k t n) * t
        = t * hsNormSq (X n) (cut (X n) (k n) t) := by
          rw [cutSeq_apply]; ring
      _ ≤ hsNormSq (X n) (k n) := h
  have hlim : Tendsto (fun n ↦ hsNormSq (X n) (k n) / t) l (nhds 0) := by
    simpa using hk.div_const t
  exact squeeze_zero'
    (Eventually.of_forall fun n ↦ hsNormSq_nonneg (X n) _)
    (Eventually.of_forall hb) hlim

/-- **Clause 1, sequence level.**  The cut moves its own sequence by at most
the square root of the threshold, uniformly over the coordinates. -/
theorem norm_sub_mul_cutSeq_le (k : ModelBoundedSequence X) {t : ℝ}
    (ht : 0 < t) :
    ‖k - k * cutSeq X k t‖ ≤ Real.sqrt t := by
  refine (lp.isLUB_norm (k - k * cutSeq X k t)).2 ?_
  rintro _ ⟨n, rfl⟩
  show ‖(k - k * cutSeq X k t) n‖ ≤ Real.sqrt t
  have hfac : (k - k * cutSeq X k t) n = k n * (1 - cut (X n) (k n) t) := by
    show k n - k n * cut (X n) (k n) t = _
    rw [Matrix.mul_sub, Matrix.mul_one]
  rw [hfac]
  have hsq := norm_mul_one_sub_cut_sq_le (X n) (k n) ht.le
  have hx := norm_nonneg (k n * (1 - cut (X n) (k n) t))
  nlinarith [Real.mul_self_sqrt ht.le, Real.sqrt_nonneg t]

/-! ## The C-star identity -/

/-- **The C-star identity for the quotient norm, hard direction.**  The
approximate unit of the ideal closes the gap between the infimum over
representatives and the star-multiplicativity of the coordinate norms. -/
theorem norm_sq_le_norm_star_mul_self (x : TracialMatrixQuotient X l) :
    ‖x‖ * ‖x‖ ≤ ‖star x * x‖ := by
  refine _root_.le_of_forall_pos_le_add ?_
  intro ε hε
  have hδpos : 0 < ε / 2 := by positivity
  obtain ⟨b, hbmk⟩ := tracialMatrixQuotientMk_surjective X l x
  obtain ⟨r, hrmk, hrn⟩ :=
    Submodule.Quotient.norm_mk_lt (star x * x) hδpos
  have hrmk' : tracialMatrixQuotientMk X l r = star x * x := hrmk
  have hkmk : tracialMatrixQuotientMk X l (star b * b) = star x * x := by
    -- The spelling bridge is done by defeq type ascription, exactly as in
    -- `hrmk'` above: `star_mk` is stated at `Ideal.Quotient.mk`, the goal at
    -- `tracialMatrixQuotientMk`, and the ascribed `have` converts silently.
    have hstarb : tracialMatrixQuotientMk X l (star b)
        = star (tracialMatrixQuotientMk X l b) :=
      (tracialMatrixQuotient_star_mk X l b).symm
    rw [map_mul, hstarb, hbmk]
  have hkJ : IsHilbertSchmidtNull X l (r - star b * b) := by
    refine (tracialMatrixQuotientMk_eq_zero_iff X l _).mp ?_
    rw [map_sub, hrmk', hkmk, sub_self]
  have htpos : 0 < ε / 2 * (ε / 2) := by positivity
  have heJ : IsHilbertSchmidtNull X l (cutSeq X (r - star b * b)
      (ε / 2 * (ε / 2))) :=
    isHilbertSchmidtNull_cutSeq X l hkJ htpos
  have hkmove : ‖(r - star b * b)
      - (r - star b * b) * cutSeq X (r - star b * b) (ε / 2 * (ε / 2))‖
      ≤ ε / 2 := by
    have h := norm_sub_mul_cutSeq_le X (r - star b * b) htpos
    rwa [Real.sqrt_mul_self hδpos.le] at h
  set e : ModelBoundedSequence X :=
    cutSeq X (r - star b * b) (ε / 2 * (ε / 2)) with he
  have hbeJ : IsHilbertSchmidtNull X l (b * e) :=
    IsHilbertSchmidtNull.mul_left X l b heJ
  have hxle : ‖x‖ ≤ ‖b - b * e‖ := by
    have hmk : tracialMatrixQuotientMk X l (b - b * e) = x := by
      rw [map_sub, hbmk,
        (tracialMatrixQuotientMk_eq_zero_iff X l _).mpr hbeJ, sub_zero]
    calc ‖x‖ = ‖tracialMatrixQuotientMk X l (b - b * e)‖ := by rw [hmk]
      _ ≤ ‖b - b * e‖ := Submodule.Quotient.norm_mk_le _ _
  have hcoordb : ∀ n, ‖(b - b * e) n‖ * ‖(b - b * e) n‖
      ≤ ‖star x * x‖ + 2 * (ε / 2) := by
    intro n
    have hproj := cut_isOrthogonalProjection (X n) ((r - star b * b) n)
      (ε / 2 * (ε / 2))
    have hermit : ((1 : Matrix (X n) (X n) ℂ) - e n)ᴴ = 1 - e n :=
      (one_sub_isOrthogonalProjection hproj).1
    have hnorm1e : ‖(1 : Matrix (X n) (X n) ℂ) - e n‖ ≤ 1 :=
      norm_le_one_of_isOrthogonalProjection
        (one_sub_isOrthogonalProjection hproj)
    have hfac : (b - b * e) n = b n * (1 - e n) := by
      show b n - b n * e n = _
      rw [Matrix.mul_sub, Matrix.mul_one]
    have hsq : ‖b n * (1 - e n)‖ * ‖b n * (1 - e n)‖
        = ‖(1 - e n) * ((b n)ᴴ * b n) * (1 - e n)‖ := by
      have hexpand : (b n * (1 - e n))ᴴ * (b n * (1 - e n))
          = (1 - e n) * ((b n)ᴴ * b n) * (1 - e n) := by
        rw [Matrix.conjTranspose_mul, hermit]
        noncomm_ring
      rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hexpand]
    have hstarco : (star b * b) n = (b n)ᴴ * b n := by
      show (star b) n * b n = _
      rw [lp.star_apply, Matrix.star_eq_conjTranspose]
    have hbr : (b n)ᴴ * b n = r n - (r - star b * b) n := by
      show (b n)ᴴ * b n = r n - (r n - (star b * b) n)
      rw [hstarco]
      exact (sub_sub_cancel _ _).symm
    have hmid : (1 - e n) * ((b n)ᴴ * b n) * (1 - e n)
        = (1 - e n) * r n * (1 - e n)
          - (1 - e n) * ((r - star b * b) n) * (1 - e n) := by
      rw [hbr]
      noncomm_ring
    have hb1 : ‖(1 - e n) * r n * (1 - e n)‖ ≤ ‖r‖ := by
      have h1 : ‖(1 - e n) * r n‖ ≤ ‖1 - e n‖ * ‖r n‖ := norm_mul_le _ _
      have h2 : ‖(1 - e n) * r n * (1 - e n)‖
          ≤ ‖(1 - e n) * r n‖ * ‖1 - e n‖ := norm_mul_le _ _
      have h3 : ‖r n‖ ≤ ‖r‖ :=
        boundedMatrixSequence_coord_norm_le (fun n ↦ X n) r n
      nlinarith [norm_nonneg ((1 : Matrix (X n) (X n) ℂ) - e n),
        norm_nonneg (r n), norm_nonneg ((1 - e n) * r n)]
    have hb2 : ‖(1 - e n) * ((r - star b * b) n) * (1 - e n)‖ ≤ ε / 2 := by
      have hco : ((r - star b * b) - (r - star b * b) * e) n
          = (r - star b * b) n * (1 - e n) := by
        show (r - star b * b) n - (r - star b * b) n * e n = _
        rw [Matrix.mul_sub, Matrix.mul_one]
      have hk1 : ‖(r - star b * b) n * (1 - e n)‖ ≤ ε / 2 := by
        calc ‖(r - star b * b) n * (1 - e n)‖
            = ‖((r - star b * b) - (r - star b * b) * e) n‖ := by rw [hco]
          _ ≤ ‖(r - star b * b) - (r - star b * b) * e‖ :=
              boundedMatrixSequence_coord_norm_le (fun n ↦ X n) _ n
          _ ≤ ε / 2 := hkmove
      have hassoc : (1 - e n) * ((r - star b * b) n) * (1 - e n)
          = (1 - e n) * (((r - star b * b) n) * (1 - e n)) := by
        noncomm_ring
      calc ‖(1 - e n) * ((r - star b * b) n) * (1 - e n)‖
          = ‖(1 - e n) * (((r - star b * b) n) * (1 - e n))‖ := by
            rw [hassoc]
        _ ≤ ‖1 - e n‖ * ‖((r - star b * b) n) * (1 - e n)‖ :=
            norm_mul_le _ _
        _ ≤ 1 * (ε / 2) := by
            have h0 := norm_nonneg (((r - star b * b) n) * (1 - e n))
            nlinarith
        _ = ε / 2 := by ring
    rw [hfac, hsq, hmid]
    calc ‖(1 - e n) * r n * (1 - e n)
          - (1 - e n) * ((r - star b * b) n) * (1 - e n)‖
        ≤ ‖(1 - e n) * r n * (1 - e n)‖
          + ‖(1 - e n) * ((r - star b * b) n) * (1 - e n)‖ :=
          norm_sub_le _ _
      _ ≤ ‖r‖ + ε / 2 := by linarith
      _ ≤ (‖star x * x‖ + ε / 2) + ε / 2 := by linarith [hrn]
      _ = ‖star x * x‖ + 2 * (ε / 2) := by ring
  have hnn : (0 : ℝ) ≤ ‖star x * x‖ + 2 * (ε / 2) := by positivity
  have hbe : ‖b - b * e‖ ≤ Real.sqrt (‖star x * x‖ + 2 * (ε / 2)) := by
    refine (lp.isLUB_norm (b - b * e)).2 ?_
    rintro _ ⟨n, rfl⟩
    show ‖(b - b * e) n‖ ≤ Real.sqrt (‖star x * x‖ + 2 * (ε / 2))
    have h := hcoordb n
    nlinarith [Real.mul_self_sqrt hnn,
      Real.sqrt_nonneg (‖star x * x‖ + 2 * (ε / 2)),
      norm_nonneg ((b - b * e) n)]
  have h1 : ‖x‖ ≤ Real.sqrt (‖star x * x‖ + 2 * (ε / 2)) := hxle.trans hbe
  nlinarith [Real.mul_self_sqrt hnn, norm_nonneg x,
    Real.sqrt_nonneg (‖star x * x‖ + 2 * (ε / 2))]

end

end TracialUltraproduct
end GroupApproximation
