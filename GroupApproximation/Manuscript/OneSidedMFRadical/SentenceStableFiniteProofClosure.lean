import GroupApproximation.Analysis.CoronaProjectionOrder
import GroupApproximation.Analysis.PolarLiftingPrintedSequence

/-!
# Sentence closure for the stable-finiteness proof

This file gives standalone names to the two proof-internal assertions marked
partial in the sentence census for `lem:stable-finite`: the Gram defect of an
arbitrary bounded lift (row 116), and the complementary-corner isometry
`w + (1-q)` (row 122).  The statements expose the lift, quotient equation,
coordinate limit, complementary isometry, and its two products.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

/-! ## Row 116: a bounded lift of an isometry -/

/-- **The first two sentences in the proof of `lem:stable-finite`.**  If `a`
is an arbitrary bounded lift of `v` and `v*v=1` in the norm-matrix corona,
then the coordinate Gram defects `a_n^*a_n-1` converge to zero in norm.

This is not phrased as existence of a convenient lift: the arbitrary lift and
the equation saying that it represents `v` are explicit binders. -/
theorem manuscriptStableFiniteBoundedLiftGramDefect
    (X : ℕ → Type u) [∀ n, Fintype (X n)]
    [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]
    (v : NormMatrixCStarCorona X) (a : BoundedMatrixSequence X)
    (ha : normMatrixCStarCoronaMk X a = v)
    (hv : star v * v = 1) :
    Tendsto (fun n ↦ ‖star (a n) * a n - 1‖) cofinite (nhds 0) := by
  apply (normMatrixCStarCoronaMk_eq_zero_iff X
    (star a * a - 1)).mp
  rw [map_sub, map_mul, map_one, ← normMatrixCStarCorona_star_mk, ha, hv,
    sub_self]

/-- The eventual estimate used immediately after row 116: beyond some
coordinate the Gram defect is at most `1/2`. -/
theorem manuscriptStableFiniteGramDefectEventuallyHalf
    (X : ℕ → Type u) [∀ n, Fintype (X n)]
    [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]
    (v : NormMatrixCStarCorona X) (a : BoundedMatrixSequence X)
    (ha : normMatrixCStarCoronaMk X a = v)
    (hv : star v * v = 1) :
    ∀ᶠ n in cofinite, ‖star (a n) * a n - 1‖ ≤ (1 / 2 : ℝ) := by
  have hlim := manuscriptStableFiniteBoundedLiftGramDefect X v a ha hv
  have hnear := (Metric.tendsto_nhds.mp hlim) (1 / 2 : ℝ) (by norm_num)
  filter_upwards [hnear] with n hn
  simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le

/-! ## Row 122: adjoining the complementary projection -/

/-- The two products of the printed complementary element
`sigma = w + (1-q)`.  The hypotheses `qw=w` and `wq=w` say precisely that
`w` belongs to the corner `qAq`.

The first conclusion is the sentence "`w+(1-q)` is an isometry in `A`"; the
second identifies its range projection before finiteness is applied. -/
theorem manuscriptComplementedCornerIsometryProducts
    {A : Type u} [Ring A] [StarRing A]
    {q w : A} (hq : IsStarProjection q)
    (hqw : q * w = w) (hwq : w * q = w)
    (hw : star w * w = q) :
    star (w + (1 - q)) * (w + (1 - q)) = 1 ∧
      (w + (1 - q)) * star (w + (1 - q)) =
        w * star w + (1 - q) := by
  have hsq : star q = q := hq.isSelfAdjoint.star_eq
  have hq2 : q * q = q := hq.isIdempotentElem.eq
  have hswq : star w * q = star w := by
    have h := congrArg star hqw
    rwa [star_mul, hsq] at h
  have hqsw : q * star w = star w := by
    have h := congrArg star hwq
    rwa [star_mul, hsq] at h
  have hwc : w * (1 - q) = 0 := by
    rw [mul_sub, mul_one, hwq, sub_self]
  have hcw : (1 - q) * w = 0 := by
    rw [sub_mul, one_mul, hqw, sub_self]
  have hswc : star w * (1 - q) = 0 := by
    rw [mul_sub, mul_one, hswq, sub_self]
  have hcsw : (1 - q) * star w = 0 := by
    rw [sub_mul, one_mul, hqsw, sub_self]
  have hc2 : (1 - q) * (1 - q) = 1 - q := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hq2, sub_self, sub_zero]
  have hstar : star (w + (1 - q)) = star w + (1 - q) := by
    rw [star_add, star_sub, star_one, hsq]
  constructor
  · calc
      star (w + (1 - q)) * (w + (1 - q)) =
          (star w + (1 - q)) * (w + (1 - q)) := by rw [hstar]
      _ = star w * w + star w * (1 - q) + (1 - q) * w +
          (1 - q) * (1 - q) := by noncomm_ring
      _ = q + 0 + 0 + (1 - q) := by rw [hw, hswc, hcw, hc2]
      _ = 1 := by abel
  · calc
      (w + (1 - q)) * star (w + (1 - q)) =
          (w + (1 - q)) * (star w + (1 - q)) := by rw [hstar]
      _ = w * star w + w * (1 - q) + (1 - q) * star w +
          (1 - q) * (1 - q) := by noncomm_ring
      _ = w * star w + 0 + 0 + (1 - q) := by rw [hwc, hcsw, hc2]
      _ = w * star w + (1 - q) := by abel

/-- **Row 122, including the reason the corner is finite.**  If every
isometry of `A` is unitary, then applying that property to the explicitly
displayed isometry `w+(1-q)` forces the corner isometry `w` to be unitary in
`qAq`, namely `w*w=q` implies `ww*=q`. -/
theorem manuscriptCornerFiniteViaComplementedIsometry
    {A : Type u} [Ring A] [StarRing A]
    (hfinite : ∀ x : A, star x * x = 1 → x * star x = 1)
    {q w : A} (hq : IsStarProjection q)
    (hqw : q * w = w) (hwq : w * q = w)
    (hw : star w * w = q) :
    let sigma := w + (1 - q)
    star sigma * sigma = 1 ∧ sigma * star sigma = 1 ∧
      w * star w = q := by
  obtain ⟨hsigma, hrange⟩ :=
    manuscriptComplementedCornerIsometryProducts hq hqw hwq hw
  have hunitary := hfinite (w + (1 - q)) hsigma
  have hcorner : w * star w = q := by
    rw [hrange] at hunitary
    refine sub_eq_zero.mp ?_
    calc
      w * star w - q = w * star w + (1 - q) - 1 := by abel
      _ = 1 - 1 := by rw [hunitary]
      _ = 0 := sub_self 1
  exact ⟨hsigma, hunitary, hcorner⟩

/-- Rows 116 and 122 are theorem schemas requiring no literature input.  This
closed package records both exact implications in one auditable proposition. -/
def StableFiniteProofSentenceCluster : Prop :=
  (∀ (X : ℕ → Type u) [∀ n, Fintype (X n)]
      [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]
      (v : NormMatrixCStarCorona X) (a : BoundedMatrixSequence X),
      normMatrixCStarCoronaMk X a = v → star v * v = 1 →
        Tendsto (fun n ↦ ‖star (a n) * a n - 1‖) cofinite (nhds 0)) ∧
    (∀ (A : Type u) [Ring A] [StarRing A]
      (_hfinite : ∀ x : A, star x * x = 1 → x * star x = 1)
      (q w : A), IsStarProjection q → q * w = w → w * q = w →
        star w * w = q → w * star w = q)

/-- Closed proof package for the two stable-finiteness proof sentences. -/
theorem manuscriptStableFiniteProofSentenceCluster :
    StableFiniteProofSentenceCluster := by
  constructor
  · intro X _ _ _ v a ha hv
    exact manuscriptStableFiniteBoundedLiftGramDefect X v a ha hv
  · intro A _ _ hfinite q w hq hqw hwq hw
    exact manuscriptCornerFiniteViaComplementedIsometry
      hfinite hq hqw hwq hw |>.2.2

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
