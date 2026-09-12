import GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoordinatePassage
import GroupApproximation.Analysis.CStarTakesakiCoefficient
import GroupApproximation.Analysis.CStarTensorProductConcrete
import GroupApproximation.Analysis.FilterMatrixCStarCorona

/-!
# The faithful-representation bridge for the printed corner inequality

The printed normal-Kazhdan proof obtains a lower quadratic-form bound in a
faithful Hilbert-space representation of the corner corona and then uses it as
a quotient-norm bound on coordinate representatives.  The first theorem below
is precisely that passage.  The second packages it in the bounded-matrix-
sequence language consumed by `eventually_sector_quadratic_form_ge`.

The key observation avoids any order-reflection theorem.  If `b` is
self-adjoint and

`c‖x‖² ≤ re ⟪x, π(b)x⟫`,

then `T = π(b - c·1)` has nonnegative numerical range.  The already proved
numerical-range estimate gives

`‖‖T‖·1 - T‖ ≤ ‖T‖`.

Faithfulness makes `π` isometric.  With `t = ‖b-c·1‖+c`, this is exactly
`‖t·1-b‖ ≤ t-c`, the norm form required by the coordinate passage.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

universe u v

/-- The printed Gram element is self-adjoint before passing to any quotient. -/
theorem sectorGram_isSelfAdjoint
    {Y ι : Type*} [Fintype Y] [DecidableEq Y]
    (S : Finset ι) (W : ι → Matrix Y Y ℂ) :
    IsSelfAdjoint (sectorGram S W) := by
  rw [IsSelfAdjoint, sectorGram, star_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [star_mul, ← Matrix.star_eq_conjTranspose, star_star]

/-- A faithful Hilbert-space representation transports the printed lower
quadratic-form bound back to the C-star algebra as the exact norm-form lower
bound used by `CornerCoordinatePassage`.

No order instance and no order-reflection hypothesis occur in the statement. -/
theorem normFormLowerBound_of_faithful_quadraticForm
    {A : Type u} [CStarAlgebra A]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (pi : A →⋆ₐ[ℂ] (E →L[ℂ] E)) (hpi : Function.Injective pi)
    {b : A} (hb : IsSelfAdjoint b) (c : ℝ)
    (hquad : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ (⟪x, pi b x⟫_ℂ).re) :
    let t : ℝ := ‖b - (c : ℂ) • (1 : A)‖ + c
    ‖(t : ℂ) • (1 : A) - b‖ ≤ t - c := by
  let r : A := b - (c : ℂ) • (1 : A)
  let t : ℝ := ‖r‖ + c
  have hnormr : ‖pi r‖ = ‖r‖ :=
    NonUnitalStarAlgHom.norm_map pi hpi r
  have hrsa : IsSelfAdjoint r := by
    dsimp [r]
    rw [IsSelfAdjoint, star_sub, star_smul, star_one, hb.star_eq]
    simp
  have hpositive : ∀ x : E, 0 ≤ (⟪x, pi r x⟫_ℂ).re := by
    intro x
    have happly : pi r x = pi b x - (c : ℂ) • x := by
      rw [show r = b - (c : ℂ) • (1 : A) by rfl, map_sub, map_smul,
        map_one]
      rfl
    have hreal : (⟪x, pi r x⟫_ℂ).re =
        (⟪x, pi b x⟫_ℂ).re - c * ‖x‖ ^ 2 := by
      rw [happly, inner_sub_right, inner_smul_right, Complex.sub_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      have hselfRe : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
        exact CStarTensor.re_inner_self x
      have hselfIm : (⟪x, x⟫_ℂ).im = 0 := by
        exact CStarTensor.im_inner_self x
      rw [hselfRe, hselfIm]
      ring
    rw [hreal]
    linarith [hquad x]
  have hop := CStarTensor.norm_smul_one_sub_le_of_isAdjoint (T := pi r) (by
    have h := (CStarTensor.StarRep.ofStarAlgHom pi).isAdjoint_star r
    simpa [hrsa.star_eq] using h) hpositive
  have hmap : pi ((t : ℂ) • (1 : A) - b) =
      (‖pi r‖ : ℂ) • (1 : E →L[ℂ] E) - pi r := by
    have hsource : (t : ℂ) • (1 : A) - b =
        (‖r‖ : ℂ) • (1 : A) - r := by
      dsimp [t, r]
      module
    rw [hsource, map_sub, map_smul, map_one, hnormr]
  change ‖(t : ℂ) • (1 : A) - b‖ ≤ t - c
  calc
    ‖(t : ℂ) • (1 : A) - b‖
        = ‖pi ((t : ℂ) • (1 : A) - b)‖ :=
          (NonUnitalStarAlgHom.norm_map pi hpi _).symm
    _ = ‖(‖pi r‖ : ℂ) • (1 : E →L[ℂ] E) - pi r‖ := by rw [hmap]
    _ ≤ ‖pi r‖ := hop
    _ = ‖r‖ := hnormr
    _ = t - c := by dsimp [t]; ring

/-- The preceding faithful-representation result in the exact coordinate
language required by `eventually_sector_quadratic_form_ge`.

`bseq` is not an opaque analytic hypothesis: it is the bounded sequence whose
coordinates are definitionally the printed Gram elements `b_n`.  The theorem
constructs the defect sequence `a_n = t·1-b_n` and proves both that coordinate
formula and its corona norm bound. -/
theorem exists_coordinateNormBound_of_faithful_cornerKazhdan
    (X : ℕ → Type u) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    [∀ n, Nonempty (X n)]
    (l : Filter ℕ) [Filter.NeBot l]
    {ι : Type*} (S : Finset ι)
    (W : ∀ n, ι → Matrix (X n) (X n) ℂ)
    (bseq : BoundedMatrixSequence X)
    (hbseq : ∀ n, bseq n = sectorGram S (W n))
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (pi : FilterMatrixCStarCorona X l →⋆ₐ[ℂ] (E →L[ℂ] E))
    (hpi : Function.Injective pi) (c : ℝ)
    (hquad : ∀ x : E, c * ‖x‖ ^ 2 ≤
      (⟪x, pi (filterMatrixCStarCoronaMk X l bseq) x⟫_ℂ).re) :
    ∃ (t : ℝ) (a : BoundedMatrixSequence X),
      (∀ n, a n = (t : ℂ) • (1 : Matrix (X n) (X n) ℂ) -
        sectorGram S (W n)) ∧
      ‖Ideal.Quotient.mk (nullMatrixSequenceIdeal X l) a‖ ≤ t - c := by
  let b : FilterMatrixCStarCorona X l :=
    filterMatrixCStarCoronaMk X l bseq
  let r : FilterMatrixCStarCorona X l := b - (c : ℂ) • 1
  let t : ℝ := ‖r‖ + c
  let a : BoundedMatrixSequence X := (t : ℂ) • 1 - bseq
  have hbseqsa : IsSelfAdjoint bseq := by
    rw [IsSelfAdjoint]
    apply Subtype.ext
    funext n
    change star (bseq n) = bseq n
    rw [hbseq n]
    exact (sectorGram_isSelfAdjoint S (W n)).star_eq
  have hb : IsSelfAdjoint b := by
    show star (filterMatrixCStarCoronaMk X l bseq) =
      filterMatrixCStarCoronaMk X l bseq
    rw [filterMatrixCStarCorona_star_mk, hbseqsa.star_eq]
  refine ⟨t, a, ?_, ?_⟩
  · intro n
    change (t : ℂ) • (1 : Matrix (X n) (X n) ℂ) - bseq n =
      (t : ℂ) • (1 : Matrix (X n) (X n) ℂ) - sectorGram S (W n)
    rw [hbseq n]
  · have hlower := normFormLowerBound_of_faithful_quadraticForm
      pi hpi hb c hquad
    change ‖filterMatrixCStarCoronaMk X l a‖ ≤ t - c
    have hclass : filterMatrixCStarCoronaMk X l a =
        (t : ℂ) • (1 : FilterMatrixCStarCorona X l) - b := by
      change filterMatrixCStarCoronaQuotient X l a =
        (t : ℂ) • (1 : FilterMatrixCStarCorona X l) - b
      rw [show a = (t : ℂ) • (1 : BoundedMatrixSequence X) - bseq by rfl,
        map_sub, map_smul, map_one]
      rfl
    rw [hclass]
    dsimp only at hlower
    have ht : t = ‖b - (c : ℂ) •
        (1 : FilterMatrixCStarCorona X l)‖ + c := by
      rfl
    rw [ht]
    exact hlower

/-- **The missing `hnorm` bridge, composed with the coordinate trace step.**

Starting with the faithful-representation quadratic-form inequality for the
actual corona class of the printed coordinate elements, this theorem concludes
the displayed normalized-corner trace inequality.  Unlike
`eventually_printed_corner_trace_inequality`, its statement contains no
quotient-norm hypothesis: that bound is constructed internally by
`normFormLowerBound_of_faithful_quadraticForm`. -/
theorem eventually_printed_corner_trace_inequality_of_faithful
    (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]
    (l : Filter ℕ) [Filter.NeBot l]
    {ι : Type*} (S : Finset ι)
    (W : ∀ n, ι → Matrix (Y n) (Y n) ℂ)
    (bseq : BoundedMatrixSequence (fun n ↦ Y n))
    (hbseq : ∀ n, bseq n = sectorGram S (W n))
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E]
    (pi : FilterMatrixCStarCorona (fun n ↦ Y n) l →⋆ₐ[ℂ] (E →L[ℂ] E))
    (hpi : Function.Injective pi) (c : ℝ)
    (hquad : ∀ x : E, c * ‖x‖ ^ 2 ≤
      (⟪x, pi (filterMatrixCStarCoronaMk (fun n ↦ Y n) l bseq) x⟫_ℂ).re)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n in l, (c - epsilon) / S.card ≤
      (S.card : ℝ)⁻¹ * ∑ s ∈ S, hsNormSq (Y n) (W n s - 1) := by
  obtain ⟨t, a, hrep, hnorm⟩ :=
    exists_coordinateNormBound_of_faithful_cornerKazhdan
      (fun n ↦ Y n) l S W bseq hbseq pi hpi c hquad
  exact eventually_printed_corner_trace_inequality
    Y l S W a t c hrep hnorm hepsilon

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
