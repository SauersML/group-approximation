import GroupApproximation.Analysis.NormMatrixCoronaUnitary
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.SemiringInverse

/-!
# KT.06: the norm ultraproduct `B_ω` is finite

This file certifies step **KT.06** of the ultraproduct proof printed in
`non_mf_groups_exist.tex` for the Kazhdan transport result,
captioned *Kazhdan transport of Hilbert--Schmidt asymptotic commutants*.  The
step lives in the paragraph of that proof beginning `\emph{The ultraproduct.}`
(grep for the sentence "The algebra $B_\omega$ is \emph{finite}").  Line
numbers are deliberately not cited: the manuscript is under concurrent
revision and only the label and the quoted sentences are stable.

The manuscript sentence being formalized is

> The algebra `B_ω` is *finite*.  Indeed, suppose `σ = [σ_n]_ω` satisfies
> `σ*σ = 1`.  Then `‖σ_n*σ_n − 1‖ → 0` along `ω`, and each `σ_n` acts on a
> finite-dimensional space.  Polar correction therefore replaces `σ_n` by a
> unitary `w_n` with `‖σ_n − w_n‖ → 0`.  Hence `σ = [w_n]_ω` is unitary.

`B_ω` is the repo's `NormMatrixCStarCorona`, the genuine C-star quotient
`ℓ∞(M_{d_n}(ℂ)) / c₀(M_{d_n}(ℂ))`; the manuscript's `ω` is realized as the
cofinite filter, which is legitimate because the manuscript's contradiction
argument first passes to an infinite set `I` and only then chooses `ω ∋ I`.

Two statements are proved, and they are genuinely different.

* `kt_06_ultraproduct_finite` is the manuscript's assertion verbatim
  (`σ*σ = 1 → σσ* = 1`), and it is proved by the manuscript's argument:
  `kt_06_polar_correction` produces the coordinatewise unitary sequence
  `(w_n)` by finite-dimensional polar correction
  (`KazhdanCornerMatrices.polarCorrectUnitary`) at every coordinate whose
  Gram defect is at most `1/2`, which is all but finitely many of them.

* `normMatrixCStarCorona_isDedekindFiniteMonoid` is the `Mathlib`-shaped
  instance `IsDedekindFiniteMonoid B_ω` demanded by
  `Analysis.ProperIsometryFromCompression.unitary_conjugate_eq_of_absorbs`.
  This is formally stronger than the manuscript sentence: it starts from an
  arbitrary one-sided inverse `x y = 1`, not from an isometry.  It is proved
  by the same *mechanism* — lift to coordinates, exploit that each coordinate
  is a finite-dimensional matrix algebra, and push the correction back
  through the quotient — but the coordinate correction is the Neumann inverse
  rather than the polar decomposition, since a general `a_n b_n ≈ 1` has no
  Gram matrix to correct.
-/

-- Five Mathlib names below are not used anywhere else in this corpus, so the
-- repo cannot vouch for them.  Each was checked directly against the pinned
-- Mathlib source (rev `905b95818e`, byte-identical to the `lake-manifest.json`
-- pin) and is recorded here with its declaration site, so the lead can
-- re-grep them in one pass at compile time:
--   MATHLIB-CHECKED: HasSummableGeomSeries
--     Mathlib/Analysis/SpecificLimits/Normed.lean:272 (class on `[NormedRing K]`)
--   MATHLIB-CHECKED: tsum_geometric_le_of_norm_lt_one
--     Mathlib/Analysis/SpecificLimits/Normed.lean:293
--     `‖x‖ < 1 → ‖∑' n : ℕ, x ^ n‖ ≤ ‖(1 : R)‖ - 1 + (1 - ‖x‖)⁻¹`
--     (needs only `[NormedRing R]`; declared before the section's
--      `variable [HasSummableGeomSeries R]`)
--   MATHLIB-CHECKED: geom_series_mul_neg
--     Mathlib/Analysis/SpecificLimits/Normed.lean:312
--     `‖x‖ < 1 → (∑' i : ℕ, x ^ i) * (1 - x) = 1`
--   MATHLIB-CHECKED: mul_neg_geom_series
--     Mathlib/Analysis/SpecificLimits/Normed.lean:315
--     `‖x‖ < 1 → (1 - x) * ∑' i : ℕ, x ^ i = 1`
--   MATHLIB-CHECKED: NormOneClass
--     Mathlib/Analysis/Normed/Ring/Basic.lean:165; the matrix instance arrives
--     via `CStarRing`'s priority-100 instance under `[Nontrivial E]`, which is
--     why `norm_swap_sub_one_le` carries a `[Nonempty Y]` binder.

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator ENNReal

universe u

noncomputable section

/-! ## The Neumann inverse

The perturbation input at a single coordinate.  Everything here is stated for
an arbitrary normed ring; the only instance the matrix algebras contribute is
completeness, which supplies `HasSummableGeomSeries`.
-/

section Neumann

variable {R : Type*} [NormedRing R]

/-- The Neumann series `∑ tᵏ`, which inverts `1 - t` whenever `‖t‖ < 1`. -/
def neumannInverse (t : R) : R := ∑' k : ℕ, t ^ k

@[simp] theorem neumannInverse_def (t : R) : neumannInverse t = ∑' k : ℕ, t ^ k := rfl

/-- The Neumann series is bounded by the scalar geometric series. -/
theorem norm_neumannInverse_le [NormOneClass R] {t : R} (ht : ‖t‖ < 1) :
    ‖neumannInverse t‖ ≤ (1 - ‖t‖)⁻¹ := by
  have hh : ‖∑' k : ℕ, t ^ k‖ ≤ ‖(1 : R)‖ - 1 + (1 - ‖t‖)⁻¹ :=
    tsum_geometric_le_of_norm_lt_one t ht
  have hone : ‖(1 : R)‖ = 1 := norm_one
  rw [hone] at hh
  rw [neumannInverse_def]
  linarith

variable [HasSummableGeomSeries R]

theorem neumannInverse_mul_one_sub {t : R} (ht : ‖t‖ < 1) :
    neumannInverse t * (1 - t) = 1 :=
  geom_series_mul_neg t ht

theorem one_sub_mul_neumannInverse {t : R} (ht : ‖t‖ < 1) :
    (1 - t) * neumannInverse t = 1 :=
  mul_neg_geom_series t ht

/-- Quantitative form of "the Neumann inverse of a small perturbation of `1`
is itself a small perturbation of `1`". -/
theorem norm_one_sub_neumannInverse_le_two_mul [NormOneClass R] {t : R}
    (ht : ‖t‖ ≤ 1 / 2) : ‖1 - neumannInverse t‖ ≤ 2 * ‖t‖ := by
  have ht1 : ‖t‖ < 1 := lt_of_le_of_lt ht (by norm_num)
  have hpos : (0 : ℝ) < 1 - ‖t‖ := by linarith
  have hne : (1 : ℝ) - ‖t‖ ≠ 0 := ne_of_gt hpos
  have hle2 : (1 - ‖t‖)⁻¹ ≤ 2 := by
    have h1 : (1 : ℝ) ≤ 2 * (1 - ‖t‖) := by linarith
    calc (1 - ‖t‖)⁻¹ = 1 * (1 - ‖t‖)⁻¹ := (one_mul _).symm
      _ ≤ (2 * (1 - ‖t‖)) * (1 - ‖t‖)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt (inv_pos.mpr hpos))
      _ = 2 := by rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
  have hinv : ‖neumannInverse t‖ ≤ 2 := (norm_neumannInverse_le ht1).trans hle2
  have h2 : neumannInverse t - neumannInverse t * t = 1 := by
    have hh := neumannInverse_mul_one_sub (R := R) ht1
    rwa [mul_sub, mul_one] at hh
  have hkey : (1 : R) - neumannInverse t = -(neumannInverse t * t) := by
    calc (1 : R) - neumannInverse t
        = (neumannInverse t - neumannInverse t * t) - neumannInverse t := by
          rw [h2]
      _ = -(neumannInverse t * t) := by abel
  rw [hkey, norm_neg]
  calc ‖neumannInverse t * t‖ ≤ ‖neumannInverse t‖ * ‖t‖ := norm_mul_le _ _
    _ ≤ 2 * ‖t‖ := mul_le_mul_of_nonneg_right hinv (norm_nonneg t)

end Neumann

/-! ## Perturbed Dedekind finiteness at a single coordinate -/

/-- The algebraic half of the coordinate estimate.  If `v` inverts `a * b` on
the left, then exact Dedekind finiteness of the ambient ring turns the
one-sided inverse `(v a) b = 1` into `b (v a) = 1`, and the defect of `b a`
from `1` is controlled by the defect of `v` from `1`. -/
theorem norm_swap_sub_one_le_of_inverse {R : Type*} [NormedRing R]
    [IsDedekindFiniteMonoid R] (a b v : R) (hv : v * (a * b) = 1) :
    ‖b * a - 1‖ ≤ ‖b‖ * ‖1 - v‖ * ‖a‖ := by
  have hvab : (v * a) * b = 1 := by rw [mul_assoc]; exact hv
  have hswap : b * (v * a) = 1 := mul_eq_one_symm hvab
  have hkey : b * a - 1 = b * (1 - v) * a := by
    have hexp : b * (1 - v) * a = b * a - b * (v * a) := by noncomm_ring
    rw [hexp, hswap]
  rw [hkey]
  calc ‖b * (1 - v) * a‖ ≤ ‖b * (1 - v)‖ * ‖a‖ := norm_mul_le _ _
    _ ≤ ‖b‖ * ‖1 - v‖ * ‖a‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg a)

/-- **The finite-dimensional coordinate step.**  In a matrix algebra, a
one-sided inverse that is only approximate is still approximately two-sided,
with an explicit constant.  This is the finite-dimensional input the
manuscript invokes as "each `σ_n` acts on a finite-dimensional space":
`Matrix Y Y ℂ` is Dedekind finite, and the Neumann series repairs the
inexactness. -/
theorem norm_swap_sub_one_le {Y : Type*} [Fintype Y] [DecidableEq Y]
    (hne : Nonempty Y) (a b : Matrix Y Y ℂ) (h : ‖a * b - 1‖ ≤ 1 / 2) :
    ‖b * a - 1‖ ≤ 2 * ‖a‖ * ‖b‖ * ‖a * b - 1‖ := by
  have hrev : ‖(1 : Matrix Y Y ℂ) - a * b‖ = ‖a * b - 1‖ := norm_sub_rev _ _
  have ht : ‖(1 : Matrix Y Y ℂ) - a * b‖ ≤ 1 / 2 := by rw [hrev]; exact h
  have ht1 : ‖(1 : Matrix Y Y ℂ) - a * b‖ < 1 := lt_of_le_of_lt ht (by norm_num)
  have hone : (1 : Matrix Y Y ℂ) - ((1 : Matrix Y Y ℂ) - a * b) = a * b := by
    abel
  have hv : neumannInverse ((1 : Matrix Y Y ℂ) - a * b) * (a * b) = 1 := by
    have hh := neumannInverse_mul_one_sub (R := Matrix Y Y ℂ) ht1
    rwa [hone] at hh
  have hnv : ‖(1 : Matrix Y Y ℂ) -
      neumannInverse ((1 : Matrix Y Y ℂ) - a * b)‖ ≤ 2 * ‖a * b - 1‖ := by
    have hh := norm_one_sub_neumannInverse_le_two_mul
      (R := Matrix Y Y ℂ) ht
    rwa [hrev] at hh
  have hmain := norm_swap_sub_one_le_of_inverse a b
    (neumannInverse ((1 : Matrix Y Y ℂ) - a * b)) hv
  calc ‖b * a - 1‖
      ≤ ‖b‖ * ‖(1 : Matrix Y Y ℂ) -
          neumannInverse ((1 : Matrix Y Y ℂ) - a * b)‖ * ‖a‖ := hmain
    _ ≤ ‖b‖ * (2 * ‖a * b - 1‖) * ‖a‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hnv (norm_nonneg b)) (norm_nonneg a)
    _ = 2 * ‖a‖ * ‖b‖ * ‖a * b - 1‖ := by ring

/-! ## `B_ω` is Dedekind finite -/

variable (X : ℕ → Type u) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
  [∀ n, Nonempty (X n)]

/-- Coordinates of a multiplicative defect in the bounded-sequence
numerator. -/
@[simp] theorem boundedMatrixSequence_mul_sub_one_apply
    (a b : BoundedMatrixSequence X) (n : ℕ) :
    (a * b - 1) n = a n * b n - 1 := rfl

/-- The coordinatewise estimate assembles into a statement about the null
ideal at **any** filter: if `a b` is asymptotically the identity along `l`, so
is `b a`.  Nothing in the Neumann-series estimate above is special to the
cofinite filter, which is what lets the same argument serve `B_c` and `B_ω`. -/
theorem isNullMatrixSequence_swap (l : Filter ℕ)
    {a b : BoundedMatrixSequence X} (hab : IsNullMatrixSequence X l (a * b - 1)) :
    IsNullMatrixSequence X l (b * a - 1) := by
  have hab' : Tendsto (fun n ↦ ‖(a * b - 1) n‖) l (nhds 0) := hab
  have hhalf : ∀ᶠ n in l, ‖(a * b - 1) n‖ ≤ (1 / 2 : ℝ) := by
    have hnear := (Metric.tendsto_nhds.mp hab') (1 / 2 : ℝ) (by norm_num)
    filter_upwards [hnear] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  show Tendsto (fun n ↦ ‖(b * a - 1) n‖) l (nhds 0)
  have hsq : Tendsto (fun n ↦ 2 * ‖a‖ * ‖b‖ * ‖(a * b - 1) n‖) l
      (nhds 0) := by
    simpa only [mul_zero] using hab'.const_mul (2 * ‖a‖ * ‖b‖)
  have hle : ∀ᶠ n in l,
      ‖(b * a - 1) n‖ ≤ 2 * ‖a‖ * ‖b‖ * ‖(a * b - 1) n‖ := by
    filter_upwards [hhalf] with n hn
    show ‖b n * a n - 1‖ ≤ 2 * ‖a‖ * ‖b‖ * ‖a n * b n - 1‖
    have hcoord : ‖b n * a n - 1‖ ≤ 2 * ‖a n‖ * ‖b n‖ * ‖a n * b n - 1‖ :=
      norm_swap_sub_one_le (by infer_instance) (a n) (b n) hn
    have h1 : ‖a n‖ ≤ ‖a‖ := (lp.isLUB_norm a).1 ⟨n, rfl⟩
    have h2 : ‖b n‖ ≤ ‖b‖ := (lp.isLUB_norm b).1 ⟨n, rfl⟩
    have hconst : 2 * ‖a n‖ * ‖b n‖ ≤ 2 * ‖a‖ * ‖b‖ :=
      mul_le_mul (by linarith) h2 (norm_nonneg _) (by positivity)
    exact hcoord.trans
      (mul_le_mul_of_nonneg_right hconst (norm_nonneg (a n * b n - 1)))
  exact squeeze_zero'
    (Eventually.of_forall fun n ↦ norm_nonneg ((b * a - 1) n)) hle hsq

/-- **KT.06 (Mathlib interface form).**  The norm-matrix C-star corona is
Dedekind finite: a one-sided inverse in `B_ω` is automatically two-sided.

This is the hypothesis consumed by
`ProperProjectionCompression.unitary_conjugate_eq_of_absorbs`, which is the
formalized endgame of the manuscript's one-sided compression step. -/
instance normMatrixCStarCorona_isDedekindFiniteMonoid :
    IsDedekindFiniteMonoid (NormMatrixCStarCorona X) where
  mul_eq_one_symm {x y} hxy := by
    obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective X x
    obtain ⟨b, rfl⟩ := normMatrixCStarCoronaMk_surjective X y
    have h0 : normMatrixCStarCoronaMk X (a * b - 1) = 0 := by
      rw [map_sub, map_mul, map_one]
      exact sub_eq_zero.mpr hxy
    have hab : IsNullMatrixSequence X cofinite (a * b - 1) :=
      (normMatrixCStarCoronaMk_eq_zero_iff X _).mp h0
    have hba : IsNullMatrixSequence X cofinite (b * a - 1) :=
      isNullMatrixSequence_swap X cofinite hab
    have h1 : normMatrixCStarCoronaMk X (b * a - 1) = 0 :=
      (normMatrixCStarCoronaMk_eq_zero_iff X _).mpr hba
    rw [map_sub, map_mul, map_one] at h1
    exact sub_eq_zero.mp h1

/-- The isometry form of the previous instance: in `B_ω` every isometry is a
unitary. -/
theorem normMatrixCStarCorona_mul_star_eq_one
    {sigma : NormMatrixCStarCorona X} (h : star sigma * sigma = 1) :
    sigma * star sigma = 1 :=
  mul_eq_one_symm h

/-! ## KT.06 as printed: the polar-correction argument

The manuscript does not argue through an abstract one-sided inverse.  It
starts from an isometry `σ`, observes that its coordinate Gram defects tend to
zero, and applies finite-dimensional polar correction at every coordinate,
producing an honestly unitary sequence `(w_n)` representing `σ`.  That is what
the two theorems below do.
-/

section Polar

variable (Z : ℕ → FiniteModel) [∀ n, Nonempty (Z n)]

/-- **KT.06 (polar correction).**  If `σ = [σ_n]` satisfies `σ*σ = 1`, then
`‖σ_n*σ_n − 1‖ → 0`, so all but finitely many coordinates have Gram defect at
most `1/2`; polar correction replaces those coordinates by genuine unitaries
`w_n` with `‖σ_n − w_n‖ → 0`, and the remaining finitely many coordinates may
be replaced by the identity.  Hence `σ = [w_n]` for a coordinatewise unitary
sequence `(w_n)`.

This is the manuscript's sentence
"Polar correction therefore replaces `σ_n` by a unitary `w_n` with
`‖σ_n − w_n‖ → 0`.  Hence `σ = [w_n]_ω`." -/
theorem kt_06_polar_correction
    {sigma : NormMatrixCStarCorona (fun n ↦ Z n)}
    (hsigma : star sigma * sigma = 1) :
    ∃ w : ∀ n, Matrix.unitaryGroup (Z n) ℂ,
      normMatrixCStarCoronaMk (fun n ↦ Z n) (unitarySequenceBounded Z w) =
        sigma := by
  obtain ⟨a, rfl⟩ := normMatrixCStarCoronaMk_surjective (fun n ↦ Z n) sigma
  have hstarmul :
      normMatrixCStarCoronaMk (fun n ↦ Z n) (star a) *
          normMatrixCStarCoronaMk (fun n ↦ Z n) a = 1 := by
    rw [← normMatrixCStarCorona_star_mk (fun n ↦ (Z n : Type)) a]
    exact hsigma
  have hgramZero :
      normMatrixCStarCoronaMk (fun n ↦ Z n) (star a * a - 1) = 0 := by
    rw [map_sub, map_mul, map_one, hstarmul, sub_self]
  have hgram : IsNullMatrixSequence (fun n ↦ Z n) cofinite (star a * a - 1) :=
    (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ Z n) _).mp hgramZero
  have hgramTendsto :
      Tendsto (fun n ↦
        ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖) cofinite (nhds 0) := by
    simpa [IsNullMatrixSequence, KazhdanCornerMatrices.cornerGram,
      lp.star_apply, Matrix.star_eq_conjTranspose] using hgram
  have hgood : ∀ᶠ n in cofinite,
      ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ) := by
    have hnear := (Metric.tendsto_nhds.mp hgramTendsto)
      (1 / 2 : ℝ) (by norm_num)
    filter_upwards [hnear] with n hn
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn.le
  let w : ∀ n, Matrix.unitaryGroup (Z n) ℂ := fun n ↦
    if hn : ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ) then
      KazhdanCornerMatrices.polarCorrectUnitary (a n)
        (KazhdanCornerMatrices.cornerGram_isHermitian (a n)) hn le_rfl
    else 1
  have hdiff : IsNullMatrixSequence (fun n ↦ Z n) cofinite
      (unitarySequenceBounded Z w - a) := by
    apply squeeze_zero'
      (Eventually.of_forall fun n ↦
        norm_nonneg ((unitarySequenceBounded Z w - a) n))
    · filter_upwards [hgood] with n hn
      change ‖(w n : Matrix (Z n) (Z n) ℂ) - a n‖ ≤
        ‖a‖ * (2 * ‖KazhdanCornerMatrices.cornerGram (a n) - 1‖)
      rw [show w n = KazhdanCornerMatrices.polarCorrectUnitary (a n)
          (KazhdanCornerMatrices.cornerGram_isHermitian (a n)) hn le_rfl by
        rw [show w n = dite
            (‖KazhdanCornerMatrices.cornerGram (a n) - 1‖ ≤ (1 / 2 : ℝ))
            (fun hn ↦ KazhdanCornerMatrices.polarCorrectUnitary (a n)
              (KazhdanCornerMatrices.cornerGram_isHermitian (a n)) hn le_rfl)
            (fun _ ↦ 1) by rfl, dif_pos hn]]
      exact (KazhdanCornerMatrices.norm_polarCorrect_sub_le_mul (a n)
        (KazhdanCornerMatrices.cornerGram_isHermitian (a n))
        (norm_nonneg _) hn le_rfl).trans
          (mul_le_mul_of_nonneg_right
            ((lp.isLUB_norm a).1 ⟨n, rfl⟩) (by positivity))
    · simpa only [mul_zero] using
        (hgramTendsto.const_mul 2).const_mul ‖a‖
  refine ⟨w, ?_⟩
  rw [← sub_eq_zero, ← map_sub]
  exact (normMatrixCStarCoronaMk_eq_zero_iff (fun n ↦ Z n) _).mpr hdiff

/-- **KT.06.**  `B_ω` is finite: an isometry of the norm ultraproduct is a
unitary.  Proved exactly as printed, through the polar correction of the
previous theorem.

**What this certifies, and the two residual differences.**  The former
corona-finiteness lemma asserts exactly one thing:
that

    `B_c = ∏_n B(K_n) / ⊕_n B(K_n)`,

the quotient of the bounded family algebra by the `c₀`-sum, is a finite C-star
algebra.  That is this statement, on this algebra: `NormMatrixCStarCorona X` is
the quotient of `BoundedMatrixSequence X = ∏_n B(K_n)` by
`nullMatrixSequenceIdeal X cofinite`, whose members are exactly the families whose
operator norms tend to zero along the cofinite filter, i.e. the `c₀`-sum.  The
proof is the printed one as well: the Gram defect is eventually at most `1/2`,
polar correction replaces those coordinates by genuine unitaries
(`kt_06_polar_correction`), and the class is unchanged.

Two differences remain, both formal and both recorded rather than papered over:

* the printed lemma quantifies over abstract finite-dimensional Hilbert spaces
  `(K_n)`; this one fixes coordinates, `K_n = ℂ^{Z n}` with `B(K_n)` the matrix
  algebra.  Every finite-dimensional Hilbert space is isometric to some `ℂ^d`,
  so nothing is lost mathematically, but the quantifier is over coordinatized
  spaces;
* the printed lemma has no nonemptiness hypothesis, while `[∀ n, Nonempty (Z n)]`
  here demands every `K_n ≠ 0`.  It is not needed for the conclusion --
  `normMatrixCStarCorona_mul_star_eq_one` above proves the same implication
  without it -- but that route goes through an abstract one-sided inverse
  rather than through polar correction, so it is not the printed proof.  The
  hypothesis enters through `unitarySequenceBounded` in
  `Analysis/NormMatrixCoronaUnitary.lean`, which bounds a unitary's norm by
  `CStarRing.norm_of_mem_unitary` and so needs the coordinate algebra to be
  nontrivial.  Removing it there would make the printed route hypothesis-free.

**Not this declaration, but no longer uncertified (updated 2026-08-17).**  The
manuscript's *unnumbered* discussion following this lemma passes to a free
ultrafilter `ω`, forms `B_ω = ∏_ω B(K_n)` and the Hilbert-space ultraproduct
`K_ω`, and asserts that the action of `B_ω` on `K_ω` is faithful and that
`ran P ⊆ ran Q` is equivalent to `P ≤ Q`.  That is *not* what this declaration
says, and it used to be true that none of it was proved anywhere; the earlier
version of this docstring recorded that.  It is now proved, in
`Sofic/OmegaOperatorUltraproduct.lean`: `omegaAct_injective` is faithfulness
and `range_le_iff_mul_eq` is the projection order, both for the genuine
`ω`-indexed corona.

The reason it needed that corona is worth keeping in view, because it is a
statement about *this* algebra: faithfulness is **false** here.
`UltraproductAdjointAmbient.kt_04_norm_eq_limsup` identifies the corona norm
with `limsup_{atTop} ‖a_n‖`, so choosing `S ∈ ω` with infinite complement and
`A_n = 0` for `n ∈ S`, `A_n = 1` otherwise gives a nonzero corona class
annihilating every vector of `K_ω`.  The formalized transport chain still never
uses faithfulness, reading `Fix ⊆ V·Fix` back as `P ≤ Q` through the algebraic
absorption identities `UltraproductKazhdanProjection.kt_09_*`; what has changed
is that the printed route is now available beside it rather than absent. -/
theorem kt_06_ultraproduct_finite :
    ∀ (Z : ℕ → FiniteModel) [∀ n, Nonempty (Z n)]
      {sigma : NormMatrixCStarCorona (fun n ↦ Z n)}
      (_hsigma : star sigma * sigma = 1), sigma * star sigma = 1 := by
  intro Z _ sigma hsigma
  obtain ⟨w, rfl⟩ := kt_06_polar_correction Z hsigma
  have hww : unitarySequenceBounded Z w * star (unitarySequenceBounded Z w)
      = 1 := by
    ext n i j
    exact congrArg (fun A : Matrix (Z n) (Z n) ℂ ↦ A i j)
      (Unitary.mul_star_self_of_mem (w n).property)
  have h := congrArg (normMatrixCStarCoronaMk (fun n ↦ Z n)) hww
  rw [map_mul, map_one] at h
  rw [normMatrixCStarCorona_star_mk (fun n ↦ (Z n : Type))
    (unitarySequenceBounded Z w)]
  exact h

/-- The manuscript's conclusion in the form it is used: an isometry of `B_ω`
is a member of the unitary group. -/
theorem kt_06_mem_unitary
    {sigma : NormMatrixCStarCorona (fun n ↦ Z n)}
    (hsigma : star sigma * sigma = 1) :
    sigma ∈ unitary (NormMatrixCStarCorona (fun n ↦ Z n)) :=
  ⟨hsigma, kt_06_ultraproduct_finite Z hsigma⟩

end Polar

end

end GroupApproximation
