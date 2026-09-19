import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedSectorProof
import GroupApproximation.Kazhdan.KazhdanComplex
import GroupApproximation.Analysis.NormMatrixCorona
import GroupApproximation.Sofic.ProjectionRankFlip

/-!
# The corona-to-coordinate passage of the printed proof of `thm:normal-kazhdan`

`Manuscript/OneSidedMFRadical/PrintedSectorProof.lean` attaches a declaration
to five of the six sentences of the printed proof of `thm:normal-kazhdan`, and
records under *What is not claimed* the one it leaves open: the printed
sentence

> The coordinate elements `b_n = |S|⁻¹ ∑_{s∈S} (W_n(s) - q_n)^*(W_n(s) - q_n)`
> represent `b`,

which is what supplies the hypothesis of the trace step
(`printed_corner_trace_inequality`) from the conclusion of the corner-Kazhdan
step (`corner_kazhdan_average_sq_ge`).  Two things stand between those two
declarations, and this module supplies both.

## 1. Restriction of scalars

`corner_kazhdan_average_sq_ge` is stated over `ℝ`, because the repository's
`IsKazhdanPair` API quantifies over real Hilbert spaces, while the corner
representation is complex.  `Kazhdan/KazhdanComplex.lean` already carries the
realification apparatus -- `realifyHom`, which reads a unitary representation
on a complex Hilbert space as an orthogonal representation on the *same*
underlying set with the *same* norm, for the real inner product
`re ⟪·,·⟫`.  Composing it with `kazhdan_sum_sq_ge_of_noInvariant` gives the
Kazhdan quadratic-form bound for a complex unitary representation with the
same constant and no loss:
`complex_kazhdan_sum_sq_ge_of_noInvariant`,
`complex_kazhdan_average_sq_ge_of_noInvariant`.

The transfer is exact rather than approximate precisely because realification
changes no norms: `‖π(s)x - x‖` is one and the same real number read in either
structure.  So this half of the passage costs nothing, and nothing below
depends on a choice of real form.

## 2. Corona order to eventual coordinate inequality

This is the half that is not a triviality.  At the coordinate level `W_n` is
only an *asymptotic* representation, so no Kazhdan pair applies to it
directly: the order lives in the corona, and it must be pushed down to the
coordinates, where it holds only eventually and only with a loss.

The device is the concrete corona norm.  `Analysis/NormMatrixCorona.lean`
proves `norm_filterMatrixCorona_mk_eq_limsup`: the quotient norm of a class is
the limsup of the coordinate operator norms along the filter.  A limsup below
a bound is *eventually* below it, which is
`eventually_coordNorm_lt_of_corona_norm_lt` -- the entire "eventually, with an
`ε` loss" of the printed passage, and nothing else.

What is transported is an order relation, not a norm, so it has to be written
as one.  The spelling used here is the norm form of the order that a unital
C-star algebra always has for a bounded self-adjoint element: for `t` large
enough,

    `c ≤ b`   ⟺   `‖t·1 - b‖ ≤ t - c`.

Only the direction `‖t·1 - b‖ ≤ t - c  ⟹  quadratic form of b ≥ c` is used,
and that direction is Cauchy--Schwarz alone
(`reGram_le_norm_mul`, `sector_quadratic_form_ge_of_norm_le`): no continuous
functional calculus, no spectral order, and no `[PartialOrder]`
`[StarOrderedRing]` side instances are installed anywhere in this file.  That
is the same discipline as the module docstring of `PrintedSectorProof`, for
the same reason.

The printed justification of sentence 4 -- "the negative part of
`b_n - (κ²/|S|) q_n` converges to zero in operator norm" -- is exactly this
mechanism: the negative part is what the norm form measures, and its vanishing
along the filter is what the limsup formula delivers.

## What is proved

* `complex_kazhdan_sum_sq_ge_of_noInvariant`,
  `complex_kazhdan_average_sq_ge_of_noInvariant` -- the corner Kazhdan
  inequality for a complex unitary representation, from the real API, with the
  same control set and the same constant.
* `reGram`, `reGram_eq`, `reGram_one`, `reGram_add`, `reGram_sub`,
  `reGram_sum`, `reGram_real_smul` -- the quadratic form of a matrix in
  coordinates, and its linearity in the matrix.
* `reGram_le_norm_mul` -- Cauchy--Schwarz: the quadratic form of `A` is
  dominated by `‖A‖` times the squared Euclidean norm.
* `sectorGram`, `reGram_sectorGram` -- the coordinate element
  `b_n = ∑_{s∈S} (W_n(s) - 1)^*(W_n(s) - 1)`, and the identification of its
  quadratic form with the printed displacement sum
  `∑_{s∈S} ‖W_n(s)x - x‖²`.
* `sector_quadratic_form_ge_of_norm_le` -- the order-to-quadratic-form step at
  one coordinate.
* `eventually_coordNorm_lt_of_corona_norm_lt`,
  `eventually_coordNorm_lt_of_corona_norm_le` -- the limsup-to-eventually
  step, stated for an arbitrary filter and reusable on its own.
* `eventually_sector_quadratic_form_ge` -- the passage itself: if the
  coordinate elements `b_n` represent a corona element bounded below by `c`,
  then for every `ε > 0` the coordinate quadratic-form inequality with
  constant `c - ε` holds at every coordinate of a set in the filter.  This is
  the printed sentence, and its conclusion is verbatim the hypothesis of
  `hsNormSq_sum_ge_of_corner_quadratic_form`.
* `eventually_printed_corner_trace_inequality` -- the passage composed with
  the trace step of `PrintedSectorProof`, which is the printed displayed
  inequality `|S|⁻¹ ∑_{s∈S} ‖W_n(s) - q_n‖₂² ≥ κ²/|S| - o(1)` holding
  eventually, with the printed `o(1)` carried by `ε`.

## What is not claimed

The corona-level hypothesis itself.  Nothing below derives, from the
Hilbert-space inequality of §1, the order inequality in the corner corona that
`eventually_sector_quadratic_form_ge` takes as its hypothesis, namely

    `∃ t : ℝ, ‖(t : ℂ) • 1 - b‖ ≤ t - κ²`   in the corner corona,

for `b` the class of `n ↦ ∑_{s∈S} (W_n(s) - q_n)^*(W_n(s) - q_n)`.  Deriving
it is the printed sentence "in every representation of the corner there are no
`K`-fixed vectors, so the defining Kazhdan inequality gives this operator
inequality", and it needs a faithful representation of the corner corona
together with the passage from the vector inequality to the operator order
there -- neither of which is constructed here.  Both halves of the passage
*around* that hypothesis are unconditional.

## Manuscript status

Supplies the corona-to-coordinate passage of the printed proof of
`thm:normal-kazhdan` and the real-to-complex scalar restriction it needs, as
the implication the printed proof states.  The endpoint of
`thm:normal-kazhdan` itself is unchanged and remains
`CoronaImageNormalKazhdan`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u v

noncomputable section

/-! ## Restriction of scalars: the corner Kazhdan inequality over `ℂ`

`IsKazhdanPair` quantifies over real Hilbert spaces, and the corner
representation is complex.  `Kazhdan/KazhdanComplex.lean` reads a complex
Hilbert space as a real one for `re ⟪·,·⟫` -- the same set, the same norm --
and a unitary as a real linear isometry (`realifyHom`).  The Kazhdan
displacement bound therefore transfers with no loss in either the control set
or the constant: the two statements below are the ones of
`PrintedSectorProof` with `ℝ` replaced by `ℂ`. -/

/-- **The corner Kazhdan inequality for a complex unitary representation.**  If
a unitary representation of `K` on a complex Hilbert space has no nonzero
invariant vector, the Kazhdan pair `(S, κ)` forces the total squared
displacement over `S` to dominate `κ²‖x‖²`.

The proof is restriction of scalars and nothing else: `realifyHom π` is `π`
read on the underlying real Hilbert space, so `‖π(s)x - x‖` is one and the
same real number on both sides, and `kazhdan_sum_sq_ge_of_noInvariant`
applies verbatim. -/
theorem complex_kazhdan_sum_sq_ge_of_noInvariant {K : Type u} [Group K]
    {S : Finset K} {kappa : ℝ} (hS : IsKazhdanPair.{u, v} K S kappa)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (pi : K →* (E ≃ₗᵢ[ℂ] E))
    (hno : ∀ y : E, (∀ g : K, pi g y = y) → y = 0) (x : E) :
    kappa ^ 2 * ‖x‖ ^ 2 ≤ ∑ s ∈ S, ‖pi s x - x‖ ^ 2 := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  exact kazhdan_sum_sq_ge_of_noInvariant hS (realifyHom pi)
    (fun y hy ↦ hno y hy) x

/-- **The same, in the printed normalization.**  Dividing by `|S|` puts the
constant where the manuscript prints it: `κ²/|S|`. -/
theorem complex_kazhdan_average_sq_ge_of_noInvariant {K : Type u} [Group K]
    {S : Finset K} {kappa : ℝ} (hS : IsKazhdanPair.{u, v} K S kappa)
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (pi : K →* (E ≃ₗᵢ[ℂ] E))
    (hno : ∀ y : E, (∀ g : K, pi g y = y) → y = 0) (x : E) :
    kappa ^ 2 / S.card * ‖x‖ ^ 2
      ≤ (S.card : ℝ)⁻¹ * ∑ s ∈ S, ‖pi s x - x‖ ^ 2 := by
  letI : InnerProductSpace ℝ E := InnerProductSpace.complexToReal
  exact kazhdan_average_sq_ge_of_noInvariant hS (realifyHom pi)
    (fun y hy ↦ hno y hy) x

/-! ## The quadratic form of a matrix, in coordinates

`reGram A x` is `re ⟪x, A x⟫` written entrywise.  It is the instance-free
reading of the order relation for a self-adjoint matrix -- the same spelling
`PrintedSectorProof` uses, and for the same reason -- and it is linear in `A`,
which is all that is needed below. -/

/-- The real part of the quadratic form of a matrix at a coordinate vector:
`re ⟪x, A x⟫`, written entrywise so that no inner-product-space instance is
installed on `Y → ℂ`. -/
def reGram {Y : Type*} [Fintype Y] (A : Matrix Y Y ℂ) (x : Y → ℂ) : ℝ :=
  ∑ i : Y, (star (x i) * (A *ᵥ x) i).re

/-- `reGram` is the real part of the dot-product form, which is the shape the
Gram bridges of `Sofic/ProjectionRankFlip.lean` are stated in. -/
theorem reGram_eq {Y : Type*} [Fintype Y] (A : Matrix Y Y ℂ) (x : Y → ℂ) :
    reGram A x = (star x ⬝ᵥ (A *ᵥ x)).re := by
  show (∑ i : Y, (star (x i) * (A *ᵥ x) i).re)
      = (∑ i : Y, star (x i) * (A *ᵥ x) i).re
  rw [Complex.re_sum]

/-- The quadratic form of the identity is the squared Euclidean norm. -/
theorem reGram_one {Y : Type*} [Fintype Y] [DecidableEq Y] (x : Y → ℂ) :
    reGram (1 : Matrix Y Y ℂ) x = ∑ i : Y, Complex.normSq (x i) := by
  rw [reGram_eq, Matrix.one_mulVec]
  exact KazhdanCornerMatrices.re_dotProduct_self x

/-- The quadratic form is additive in the matrix. -/
theorem reGram_add {Y : Type*} [Fintype Y] (A B : Matrix Y Y ℂ) (x : Y → ℂ) :
    reGram (A + B) x = reGram A x + reGram B x := by
  have hstep : ∀ i : Y, (star (x i) * ((A + B) *ᵥ x) i).re
      = (star (x i) * (A *ᵥ x) i).re + (star (x i) * (B *ᵥ x) i).re := by
    intro i
    rw [Matrix.add_mulVec, Pi.add_apply, mul_add, Complex.add_re]
  calc reGram (A + B) x
      = ∑ i : Y, ((star (x i) * (A *ᵥ x) i).re
          + (star (x i) * (B *ᵥ x) i).re) := by
        simp only [reGram]
        exact Finset.sum_congr rfl fun i _ ↦ hstep i
    _ = reGram A x + reGram B x := by
        simp only [reGram]
        exact Finset.sum_add_distrib

/-- The quadratic form is additive in the matrix, in subtracted form. -/
theorem reGram_sub {Y : Type*} [Fintype Y] (A B : Matrix Y Y ℂ) (x : Y → ℂ) :
    reGram (A - B) x = reGram A x - reGram B x := by
  have h : reGram (A - B) x + reGram B x = reGram A x := by
    rw [← reGram_add, sub_add_cancel]
  linarith

/-- The quadratic form of a finite sum of matrices is the sum of the quadratic
forms.  This is what makes the printed `b_n = ∑_{s∈S} (W_n(s) - q_n)^*
(W_n(s) - q_n)` computable term by term. -/
theorem reGram_sum {Y : Type*} [Fintype Y] {ι : Type*} (S : Finset ι)
    (M : ι → Matrix Y Y ℂ) (x : Y → ℂ) :
    reGram (∑ s ∈ S, M s) x = ∑ s ∈ S, reGram (M s) x := by
  have hstep : ∀ i : Y, (star (x i) * ((∑ s ∈ S, M s) *ᵥ x) i).re
      = ∑ s ∈ S, (star (x i) * (M s *ᵥ x) i).re := by
    intro i
    rw [Matrix.sum_mulVec, Finset.sum_apply, Finset.mul_sum, Complex.re_sum]
  calc reGram (∑ s ∈ S, M s) x
      = ∑ i : Y, ∑ s ∈ S, (star (x i) * (M s *ᵥ x) i).re := by
        simp only [reGram]
        exact Finset.sum_congr rfl fun i _ ↦ hstep i
    _ = ∑ s ∈ S, ∑ i : Y, (star (x i) * (M s *ᵥ x) i).re := Finset.sum_comm
    _ = ∑ s ∈ S, reGram (M s) x := by simp only [reGram]

/-- Real scalars come out of the quadratic form. -/
theorem reGram_real_smul {Y : Type*} [Fintype Y] (t : ℝ) (A : Matrix Y Y ℂ)
    (x : Y → ℂ) : reGram ((t : ℂ) • A) x = t * reGram A x := by
  have hstep : ∀ i : Y, (star (x i) * (((t : ℂ) • A) *ᵥ x) i).re
      = t * (star (x i) * (A *ᵥ x) i).re := by
    intro i
    rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
      show star (x i) * ((t : ℂ) * (A *ᵥ x) i)
          = (t : ℂ) * (star (x i) * (A *ᵥ x) i) by ring,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc reGram ((t : ℂ) • A) x
      = ∑ i : Y, t * (star (x i) * (A *ᵥ x) i).re := by
        simp only [reGram]
        exact Finset.sum_congr rfl fun i _ ↦ hstep i
    _ = t * reGram A x := by
        simp only [reGram]
        rw [Finset.mul_sum]

/-- **Cauchy--Schwarz.**  The quadratic form of `A` is dominated by `‖A‖` times
the squared Euclidean norm.  This is the only analytic input of the passage:
it is what turns the norm form of the corona order into a lower bound on the
coordinate quadratic form, with no functional calculus. -/
theorem reGram_le_norm_mul {Y : Type*} [Fintype Y] [DecidableEq Y]
    (A : Matrix Y Y ℂ) (x : Y → ℂ) :
    reGram A x ≤ ‖A‖ * ∑ i : Y, Complex.normSq (x i) := by
  have hNnn : (0 : ℝ) ≤ ∑ i : Y, Complex.normSq (x i) :=
    Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _
  have hx : (∑ i : Y, ‖x i‖ ^ 2) = ∑ i : Y, Complex.normSq (x i) :=
    Finset.sum_congr rfl fun i _ ↦ (Complex.normSq_eq_norm_sq (x i)).symm
  have hAx : (∑ i : Y, ‖(A *ᵥ x) i‖ ^ 2)
      ≤ ‖A‖ ^ 2 * ∑ i : Y, Complex.normSq (x i) := by
    have h := KazhdanCornerMatrices.sum_normSq_mulVec_le_general A x
    refine le_trans (le_of_eq ?_) h
    exact Finset.sum_congr rfl fun i _ ↦ (Complex.normSq_eq_norm_sq _).symm
  have hcs : (∑ i : Y, ‖x i‖ * ‖(A *ᵥ x) i‖) ^ 2
      ≤ (∑ i : Y, ‖x i‖ ^ 2) * ∑ i : Y, ‖(A *ᵥ x) i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  rw [hx] at hcs
  have hprod : (∑ i : Y, ‖x i‖ * ‖(A *ᵥ x) i‖) ^ 2
      ≤ (‖A‖ * ∑ i : Y, Complex.normSq (x i)) ^ 2 := by
    calc (∑ i : Y, ‖x i‖ * ‖(A *ᵥ x) i‖) ^ 2
        ≤ (∑ i : Y, Complex.normSq (x i)) * ∑ i : Y, ‖(A *ᵥ x) i‖ ^ 2 := hcs
      _ ≤ (∑ i : Y, Complex.normSq (x i))
            * (‖A‖ ^ 2 * ∑ i : Y, Complex.normSq (x i)) :=
          mul_le_mul_of_nonneg_left hAx hNnn
      _ = (‖A‖ * ∑ i : Y, Complex.normSq (x i)) ^ 2 := by ring
  have hsumnn : (0 : ℝ) ≤ ∑ i : Y, ‖x i‖ * ‖(A *ᵥ x) i‖ :=
    Finset.sum_nonneg fun _ _ ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hrhsnn : (0 : ℝ) ≤ ‖A‖ * ∑ i : Y, Complex.normSq (x i) :=
    mul_nonneg (norm_nonneg A) hNnn
  have hfinal : (∑ i : Y, ‖x i‖ * ‖(A *ᵥ x) i‖)
      ≤ ‖A‖ * ∑ i : Y, Complex.normSq (x i) :=
    (sq_le_sq₀ hsumnn hrhsnn).mp hprod
  refine le_trans ?_ hfinal
  simp only [reGram]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  calc (star (x i) * (A *ᵥ x) i).re
      ≤ ‖star (x i) * (A *ᵥ x) i‖ := Complex.re_le_norm _
    _ = ‖x i‖ * ‖(A *ᵥ x) i‖ := by rw [norm_mul, norm_star]

/-! ## The printed coordinate element `b_n`

`sectorGram S W = ∑_{s∈S} (W(s) - 1)^*(W(s) - 1)`.  With `W = W_n` and
`1 = q_n` the identity of the corner, this is the printed `b_n` with the
factor `|S|⁻¹` left off -- the same normalization convention as
`hsNormSq_sum_ge_of_corner_quadratic_form`, which carries `|S|` on the right
and puts the printed constant back in `printed_corner_trace_inequality`. -/

/-- The printed coordinate element
`b_n = ∑_{s∈S} (W_n(s) - q_n)^*(W_n(s) - q_n)` of the corner. -/
def sectorGram {Y : Type*} [Fintype Y] [DecidableEq Y] {ι : Type*}
    (S : Finset ι) (W : ι → Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  ∑ s ∈ S, (W s - 1)ᴴ * (W s - 1)

/-- **The quadratic form of `b_n` is the printed displacement sum.**  This is
the identity that makes the order inequality for `b` and the displayed trace
inequality two readings of one statement, which is why no information is lost
by transporting the order in quadratic-form shape. -/
theorem reGram_sectorGram {Y : Type*} [Fintype Y] [DecidableEq Y] {ι : Type*}
    (S : Finset ι) (W : ι → Matrix Y Y ℂ) (x : Y → ℂ) :
    reGram (sectorGram S W) x
      = ∑ s ∈ S, ∑ i : Y, Complex.normSq ((W s *ᵥ x - x) i) := by
  simp only [sectorGram]
  rw [reGram_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hx : (W s - 1) *ᵥ x = W s *ᵥ x - x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [reGram_eq,
    ← KazhdanCornerMatrices.sum_normSq_mulVec_eq_re_gram_general (W s - 1) x,
    hx]

/-- **The order-to-quadratic-form step, at one coordinate.**  If `b_n` sits
inside the ball of radius `t - c + ε` around `t·1` -- the norm form of
`b_n ≥ (c - ε)·1`, valid for any `t` past the norm of `b_n` -- then its
quadratic form dominates `(c - ε)` times the squared Euclidean norm.

The proof is Cauchy--Schwarz applied to `t·1 - b_n`:
`t‖x‖² - reGram b_n x ≤ ‖t·1 - b_n‖ · ‖x‖² ≤ (t - c + ε)‖x‖²`. -/
theorem sector_quadratic_form_ge_of_norm_le {Y : Type*} [Fintype Y]
    [DecidableEq Y] {ι : Type*} (S : Finset ι) (W : ι → Matrix Y Y ℂ)
    (t c ε : ℝ)
    (h : ‖(t : ℂ) • (1 : Matrix Y Y ℂ) - sectorGram S W‖ ≤ t - c + ε)
    (x : Y → ℂ) :
    (c - ε) * ∑ i : Y, Complex.normSq (x i)
      ≤ ∑ s ∈ S, ∑ i : Y, Complex.normSq ((W s *ᵥ x - x) i) := by
  have hNnn : (0 : ℝ) ≤ ∑ i : Y, Complex.normSq (x i) :=
    Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _
  have hsplit : reGram ((t : ℂ) • (1 : Matrix Y Y ℂ) - sectorGram S W) x
      = t * (∑ i : Y, Complex.normSq (x i))
        - ∑ s ∈ S, ∑ i : Y, Complex.normSq ((W s *ᵥ x - x) i) := by
    rw [reGram_sub, reGram_real_smul, reGram_one, reGram_sectorGram]
  have hbound : reGram ((t : ℂ) • (1 : Matrix Y Y ℂ) - sectorGram S W) x
      ≤ (t - c + ε) * ∑ i : Y, Complex.normSq (x i) :=
    (reGram_le_norm_mul _ x).trans (mul_le_mul_of_nonneg_right h hNnn)
  rw [hsplit] at hbound
  nlinarith [hbound]

/-! ## The corona norm is a limsup, so a corona bound is an eventual one

`norm_filterMatrixCorona_mk_eq_limsup` identifies the quotient norm of a class
with the limsup of the coordinate operator norms along the filter.  A limsup
strictly below a bound is eventually below it, and that -- with nothing else
-- is the "after passing to a subsequence, with an `ε` loss" of the printed
passage. -/

/-- **A corona norm bound is an eventual coordinate norm bound.**  If the class
of `a` in the corona at `l` has norm below `y`, then `‖a n‖ < y` at every
coordinate of a set in `l`.

Reusable on its own: this is the only place the corona enters the passage. -/
theorem eventually_coordNorm_lt_of_corona_norm_lt (X : ℕ → Type u)
    [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]
    (l : Filter ℕ) [Filter.NeBot l] (a : BoundedMatrixSequence X) {y : ℝ}
    (h : ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a‖ < y) :
    ∀ᶠ n in l, ‖a n‖ < y := by
  rw [norm_filterMatrixCorona_mk_eq_limsup X l a] at h
  refine Filter.eventually_lt_of_limsup_lt h ?_
  exact ⟨‖a‖, show ∀ᶠ n : ℕ in l, ‖a n‖ ≤ ‖a‖ from
    Eventually.of_forall fun n ↦ boundedMatrixSequence_coord_norm_le X a n⟩

/-- **The same with a non-strict corona bound and an explicit loss.**  This is
the printed `o(1)`: the corona bound `y` is paid for at the coordinates by an
arbitrarily small `ε`. -/
theorem eventually_coordNorm_lt_of_corona_norm_le (X : ℕ → Type u)
    [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]
    (l : Filter ℕ) [Filter.NeBot l] (a : BoundedMatrixSequence X) {y ε : ℝ}
    (h : ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a‖ ≤ y)
    (hε : 0 < ε) : ∀ᶠ n in l, ‖a n‖ < y + ε :=
  eventually_coordNorm_lt_of_corona_norm_lt X l a
    (lt_of_le_of_lt h (by linarith))

/-! ## The passage

> The coordinate elements `b_n = |S|⁻¹ ∑_{s∈S} (W_n(s) - q_n)^*(W_n(s) - q_n)`
> represent `b`.

`hrep` is that sentence: the bounded sequence `a` whose class carries the
corona order is, coordinate by coordinate, the printed `t·1 - b_n`.  `hnorm`
is the corona order in its norm form.  The conclusion is the coordinate
quadratic-form inequality of `PrintedSectorProof`, holding at every
coordinate of a set in the filter and with the printed `o(1)` loss. -/

/-- **The corona-to-coordinate passage.**  If the coordinate elements
`b_n = ∑_{s∈S} (W_n(s) - 1)^*(W_n(s) - 1)` represent a corona element bounded
below by `c` -- written in norm form, `‖t·1 - b‖ ≤ t - c` -- then for every
`ε > 0` the coordinate quadratic-form inequality with constant `c - ε` holds
at every coordinate of a set in the filter.

The conclusion is verbatim the hypothesis of
`hsNormSq_sum_ge_of_corner_quadratic_form`, which is what the printed trace
step consumes. -/
theorem eventually_sector_quadratic_form_ge (X : ℕ → Type u)
    [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)]
    (l : Filter ℕ) [Filter.NeBot l] {ι : Type*} (S : Finset ι)
    (W : ∀ n, ι → Matrix (X n) (X n) ℂ) (a : BoundedMatrixSequence X)
    (t c : ℝ)
    (hrep : ∀ n, a n
      = (t : ℂ) • (1 : Matrix (X n) (X n) ℂ) - sectorGram S (W n))
    (hnorm : ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a‖ ≤ t - c)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in l, ∀ x : X n → ℂ,
      (c - ε) * ∑ i : X n, Complex.normSq (x i)
        ≤ ∑ s ∈ S, ∑ i : X n, Complex.normSq ((W n s *ᵥ x - x) i) := by
  have hev := eventually_coordNorm_lt_of_corona_norm_le X l a hnorm hε
  filter_upwards [hev] with n hn
  intro x
  refine sector_quadratic_form_ge_of_norm_le S (W n) t c ε ?_ x
  rw [← hrep n]
  exact le_of_lt hn

/-- **The passage composed with the printed trace step.**  With `Y n` the
corner `q_n M_{d_n}(ℂ) q_n`, `1 = q_n` its identity and `c = κ²`, this is the
manuscript's displayed inequality

    `|S|⁻¹ ∑_{s∈S} ‖W_n(s) - q_n‖₂² ≥ κ²/|S| - o(1)`,

holding at every coordinate of a set in the filter, with the printed `o(1)`
carried by `ε` and `‖·‖₂` the normalized Hilbert--Schmidt norm of the corner
(`hsNormSq`). -/
theorem eventually_printed_corner_trace_inequality (Y : ℕ → FiniteModel)
    [∀ n, Nonempty (Y n)] (l : Filter ℕ) [Filter.NeBot l] {ι : Type*} (S : Finset ι)
    (W : ∀ n, ι → Matrix (Y n) (Y n) ℂ)
    (a : BoundedMatrixSequence (fun n ↦ Y n)) (t c : ℝ)
    (hrep : ∀ n, a n
      = (t : ℂ) • (1 : Matrix (Y n) (Y n) ℂ) - sectorGram S (W n))
    (hnorm : ‖Ideal.Quotient.mk
      (nullMatrixSequenceIdeal (fun n ↦ Y n) l) a‖ ≤ t - c)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in l, (c - ε) / S.card
      ≤ (S.card : ℝ)⁻¹ * ∑ s ∈ S, hsNormSq (Y n) (W n s - 1) := by
  have hev := eventually_sector_quadratic_form_ge (fun n ↦ Y n) l S W a t c
    hrep hnorm hε
  filter_upwards [hev] with n hn
  exact printed_corner_trace_inequality (Y n) Fintype.card_pos S (W n)
    (c - ε) hn

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
