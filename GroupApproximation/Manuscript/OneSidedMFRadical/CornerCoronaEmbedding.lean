import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedRouteAnalyticFacts

/-!
# The corner of a norm matrix corona is a norm matrix corona

`non_mf_groups_exist.tex`, the rewritten proof of Lemma
`lem:central-corona-corner`:

> Unitary identifications `J_n : ℂ^{r_n} → q_n ℂ^{d_n}` identify each corner
> `q_n M_{d_n}(ℂ) q_n` with `M_{r_n}(ℂ)`, and then the corner
> `q 𝒬_d q` with the corona `𝒬_r`: a bounded sequence `(z_n)` representing
> `z ∈ 𝒬_d` gives the representative `(q_n z_n q_n)` of `q z q`.

That sentence is the one piece of the rewritten proof the development did not
carry.  `Analysis/CornerMatrixEmbedding.lean` has the *coordinatewise* half —
`cornerEmbed` is an isometric `⋆`-embedding of `M_{r_n}(ℂ)` onto
`q_n M_{d_n}(ℂ) q_n`, and `cornerCompression` is its inverse there.  This file
lifts that to sequences and records what the corona needs:

* `cornerEmbedSeq` is multiplicative, star-preserving and subtractive on
  sequences, and sends `1` to the sequence of projections;
* `norm_mk_cornerEmbedSeq` — the class of `(J_n c_n J_n*)` has the *same*
  norm as the class of `(c_n)`, because the quotient norm is a `limsup` of
  coordinate norms and `cornerEmbed` is a coordinatewise isometry.  This is
  the injectivity that makes the printed "identify the corner with the
  corona" legitimate;
* `cornerEmbedSeq_cornerCompressSeq_apply` — the printed representative:
  compressing and re-embedding a sequence is `(q_n z_n q_n)`.

Nothing here mentions a group, a representation, or an ultrafilter.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace CornerCoronaEmbedding

open Filter Matrix Topology
open PrintedCornerCompression
open KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## The coordinatewise identification, completed -/

/-- **`J_n J_n* = q_n`.**  The corner embedding sends the identity of the
corner to the projection itself. -/
theorem cornerEmbed_one {Z : Type*} [Fintype Z] [DecidableEq Z]
    {p : Matrix Z Z ℂ} (hp : p.IsHermitian) (hidem : p * p = p) :
    cornerEmbed hp (1 : Matrix {i : Z // cornerPredicate hp i}
      {i : Z // cornerPredicate hp i} ℂ) = p := by
  have h := cornerEmbed_cornerCompression hp hidem (1 : Matrix Z Z ℂ)
  rw [cornerCompression_one, Matrix.mul_one, hidem] at h
  exact h

/-- **The image of `J_n` is the corner.** -/
theorem cornerEmbed_mem_corner {Z : Type*} [Fintype Z] [DecidableEq Z]
    {p : Matrix Z Z ℂ} (hp : p.IsHermitian) (hidem : p * p = p)
    (C : Matrix {i : Z // cornerPredicate hp i}
      {i : Z // cornerPredicate hp i} ℂ) :
    p * cornerEmbed hp C * p = cornerEmbed hp C := by
  have h1 : cornerEmbed hp (1 * C * 1)
      = cornerEmbed hp 1 * cornerEmbed hp C * cornerEmbed hp 1 := by
    rw [cornerEmbed_mul, cornerEmbed_mul]
  rw [one_mul, mul_one, cornerEmbed_one hp hidem] at h1
  exact h1.symm

/-! ## The two sequence-level maps -/

variable (Y : ℕ → FiniteModel) (P : ∀ n, Matrix (Y n) (Y n) ℂ)
  (hP : ∀ n, (P n).IsHermitian)

/-- **The printed corner `q_n M_{d_n}(ℂ) q_n`**, as a finite matrix model.
The printed unitary identification `J_n : ℂ^{r_n} → q_n ℂ^{d_n}` is the
eigenbasis of `q_n` restricted to the coordinates where its eigenvalue is
`1`, which is what `PrintedCornerCompression.cornerPredicate` names. -/
abbrev cornerModel (n : ℕ) : FiniteModel :=
  ⟨{i : Y n // cornerPredicate (hP n) i}, inferInstance, inferInstance⟩

/-- **"Since `q ≠ 0`, infinitely many `q_n` are nonzero; retain those
coordinates."**  At a retained coordinate the corner is nonempty. -/
theorem cornerModel_nonempty (hidem : ∀ n, P n * P n = P n)
    (hPne : ∀ n, P n ≠ 0) (n : ℕ) : Nonempty (cornerModel Y P hP n) := by
  obtain ⟨i, hi⟩ := cornerPredicate_exists (hP n) (hidem n) (hPne n)
  exact ⟨⟨i, hi⟩⟩

theorem cornerModel_card_pos (hidem : ∀ n, P n * P n = P n)
    (hPne : ∀ n, P n ≠ 0) (n : ℕ) :
    0 < Fintype.card (cornerModel Y P hP n) := by
  obtain ⟨i, hi⟩ := cornerPredicate_exists (hP n) (hidem n) (hPne n)
  exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩

/-- **`(c_n) ↦ (J_n c_n J_n*)`.**  Zero-extension of a corner sequence into
the ambient matrices, coordinate by coordinate. -/
def cornerEmbedSeq
    (c : BoundedMatrixSequence (fun n ↦ cornerModel Y P hP n)) :
    BoundedMatrixSequence (fun n ↦ Y n) :=
  ⟨fun n ↦ cornerEmbed (hP n) (c n), memℓp_infty ⟨‖c‖, by
    rintro _ ⟨n, rfl⟩
    exact le_of_eq_of_le (norm_cornerEmbed (hP n) (c n))
      (boundedMatrixSequence_coord_norm_le
        (fun n ↦ cornerModel Y P hP n) c n)⟩⟩

@[simp] theorem cornerEmbedSeq_apply
    (c : BoundedMatrixSequence (fun n ↦ cornerModel Y P hP n)) (n : ℕ) :
    (cornerEmbedSeq Y P hP c : ∀ n, Matrix (Y n) (Y n) ℂ) n
      = cornerEmbed (hP n) (c n) := rfl

/-- **`(z_n) ↦ (q_n z_n q_n)`, in the corner coordinates.** -/
def cornerCompressSeq (a : BoundedMatrixSequence (fun n ↦ Y n)) :
    BoundedMatrixSequence (fun n ↦ cornerModel Y P hP n) :=
  ⟨fun n ↦ cornerCompression (hP n) (a n), memℓp_infty ⟨‖a‖, by
    rintro _ ⟨n, rfl⟩
    exact (norm_cornerCompression_le (hP n) (a n)).trans
      (boundedMatrixSequence_coord_norm_le (fun n ↦ Y n) a n)⟩⟩

@[simp] theorem cornerCompressSeq_apply
    (a : BoundedMatrixSequence (fun n ↦ Y n)) (n : ℕ) :
    (cornerCompressSeq Y P hP a :
        ∀ n, Matrix (cornerModel Y P hP n) (cornerModel Y P hP n) ℂ) n
      = cornerCompression (hP n) (a n) := rfl

/-- **The printed representative.**  Compressing a sequence and embedding it
back gives `(q_n z_n q_n)`, which is the printed representative of `q z q`. -/
theorem cornerEmbedSeq_cornerCompressSeq_apply
    (hidem : ∀ n, P n * P n = P n)
    (a : BoundedMatrixSequence (fun n ↦ Y n)) (n : ℕ) :
    (cornerEmbedSeq Y P hP (cornerCompressSeq Y P hP a) :
        ∀ n, Matrix (Y n) (Y n) ℂ) n
      = P n * (a n) * P n :=
  cornerEmbed_cornerCompression (hP n) (hidem n) (a n)

/-! ## `cornerEmbedSeq` is a `⋆`-embedding -/

theorem cornerEmbedSeq_mul
    (c d : BoundedMatrixSequence (fun n ↦ cornerModel Y P hP n)) :
    cornerEmbedSeq Y P hP (c * d)
      = cornerEmbedSeq Y P hP c * cornerEmbedSeq Y P hP d := by
  refine lp.ext (funext fun n ↦ ?_)
  simp only [cornerEmbedSeq_apply, lp.infty_coeFn_mul, Pi.mul_apply]
  exact cornerEmbed_mul (hP n) (c n) (d n)

theorem cornerEmbedSeq_sub
    (c d : BoundedMatrixSequence (fun n ↦ cornerModel Y P hP n)) :
    cornerEmbedSeq Y P hP (c - d)
      = cornerEmbedSeq Y P hP c - cornerEmbedSeq Y P hP d := by
  refine lp.ext (funext fun n ↦ ?_)
  simp only [cornerEmbedSeq_apply, lp.coeFn_sub, Pi.sub_apply]
  exact cornerEmbed_sub (hP n) (c n) (d n)

theorem cornerEmbedSeq_star
    (c : BoundedMatrixSequence (fun n ↦ cornerModel Y P hP n)) :
    cornerEmbedSeq Y P hP (star c) = star (cornerEmbedSeq Y P hP c) := by
  refine lp.ext (funext fun n ↦ ?_)
  simp only [cornerEmbedSeq_apply, lp.star_apply]
  rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]
  exact (cornerEmbed_conjTranspose (hP n) (c n)).symm

/-- **The corner unit.**  The embedding sends the identity of the corner
corona to the printed projection sequence `(q_n)`. -/
theorem cornerEmbedSeq_one_apply [∀ n, Nonempty (cornerModel Y P hP n)]
    (hidem : ∀ n, P n * P n = P n) (n : ℕ) :
    (cornerEmbedSeq Y P hP 1 : ∀ n, Matrix (Y n) (Y n) ℂ) n = P n := by
  have hone : ((1 : BoundedMatrixSequence (fun n ↦ cornerModel Y P hP n)) :
      ∀ n, Matrix (cornerModel Y P hP n) (cornerModel Y P hP n) ℂ) n = 1 := by
    rw [lp.infty_coeFn_one]
    rfl
  rw [cornerEmbedSeq_apply, hone]
  exact cornerEmbed_one (hP n) (hidem n)

/-! ## The embedding is isometric on classes -/

theorem norm_cornerEmbedSeq_apply
    (c : BoundedMatrixSequence (fun n ↦ cornerModel Y P hP n)) (n : ℕ) :
    ‖(cornerEmbedSeq Y P hP c : ∀ n, Matrix (Y n) (Y n) ℂ) n‖ = ‖(c n)‖ :=
  norm_cornerEmbed (hP n) (c n)

variable [∀ n, Nonempty (Y n)] [∀ n, Nonempty (cornerModel Y P hP n)]

/-- **The printed identification of the corner with the corona.**  The class
of `(J_n c_n J_n*)` has the same norm as the class of `(c_n)`, because the
quotient norm is the `limsup` of the coordinate norms and `cornerEmbed` is a
coordinatewise isometry.  In particular the passage from the corner corona to
the ambient corner is injective, which is what "identify" means. -/
theorem norm_mk_cornerEmbedSeq
    (c : BoundedMatrixSequence (fun n ↦ cornerModel Y P hP n)) :
    ‖normMatrixCStarCoronaMk (fun n ↦ Y n) (cornerEmbedSeq Y P hP c)‖
      = ‖normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n) c‖ := by
  rw [norm_normMatrixCStarCoronaMk_eq_limsup (fun n ↦ Y n)
      (cornerEmbedSeq Y P hP c),
    norm_normMatrixCStarCoronaMk_eq_limsup (fun n ↦ cornerModel Y P hP n) c]
  congr 1
  funext n
  exact norm_cornerEmbedSeq_apply Y P hP c n

/-- The injectivity, in the form the printed proof uses it. -/
theorem mk_eq_of_mk_cornerEmbedSeq_eq
    (c d : BoundedMatrixSequence (fun n ↦ cornerModel Y P hP n))
    (h : normMatrixCStarCoronaMk (fun n ↦ Y n) (cornerEmbedSeq Y P hP c)
      = normMatrixCStarCoronaMk (fun n ↦ Y n) (cornerEmbedSeq Y P hP d)) :
    normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n) c
      = normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n) d := by
  have hsubY := map_sub (normMatrixCStarCoronaMk (fun n ↦ Y n))
    (cornerEmbedSeq Y P hP c) (cornerEmbedSeq Y P hP d)
  have hsubC := map_sub
    (normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n)) c d
  have hzero : ‖normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n)
      (c - d)‖ = 0 := by
    rw [← norm_mk_cornerEmbedSeq Y P hP (c - d), cornerEmbedSeq_sub, hsubY, h,
      sub_self, norm_zero]
  have hz := norm_eq_zero.mp hzero
  rw [hsubC, sub_eq_zero] at hz
  exact hz

/-- Equal classes in the corner corona have equal images in the ambient
corona: the printed identification is a map of coronas, not merely of
sequences. -/
theorem mk_cornerEmbedSeq_congr
    (c d : BoundedMatrixSequence (fun n ↦ cornerModel Y P hP n))
    (h : normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n) c
      = normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n) d) :
    normMatrixCStarCoronaMk (fun n ↦ Y n) (cornerEmbedSeq Y P hP c)
      = normMatrixCStarCoronaMk (fun n ↦ Y n) (cornerEmbedSeq Y P hP d) := by
  have hsubY := map_sub (normMatrixCStarCoronaMk (fun n ↦ Y n))
    (cornerEmbedSeq Y P hP c) (cornerEmbedSeq Y P hP d)
  have hsubC := map_sub
    (normMatrixCStarCoronaMk (fun n ↦ cornerModel Y P hP n)) c d
  have hzero : ‖normMatrixCStarCoronaMk (fun n ↦ Y n)
      (cornerEmbedSeq Y P hP (c - d))‖ = 0 := by
    rw [norm_mk_cornerEmbedSeq Y P hP (c - d), hsubC, h, sub_self, norm_zero]
  rw [cornerEmbedSeq_sub, hsubY] at hzero
  have hz := norm_eq_zero.mp hzero
  rw [sub_eq_zero] at hz
  exact hz

end

end CornerCoronaEmbedding
end OneSidedMFRadical
end Manuscript
end GroupApproximation
