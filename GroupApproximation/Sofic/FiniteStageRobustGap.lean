import GroupApproximation.Sofic.KazhdanCornerMatrices

/-!
# Finite-stage quantitative estimates for the robust spectral gap

`non_mf_groups_exist.tex` used to prove `\ref{thm:kazhdan-transport}` a second
time, in a section titled "The finite-stage transport proof",
"quantitatively at each single coordinate `n` and with no
ultrafilter", with a remark ("The ultrafilter gives no
rate") recording that the error bookkeeping there is explicit in terms of the
Kazhdan constant `κ`, the size `|S|` of the averaging set, the uniform bound
`M` on the transported vectors, and the multiplicative defects of the
microstates, *once the robust spectral-gap input stated there is granted at
each stage*.

**Neither the section nor the remark is printed any more.**  Commit `3a45fa60`
("Editorial pass: rewrite orbit collapse, cut what nothing uses") deleted both,
after the rewritten collapse step stopped consuming the finite-stage route.
What the manuscript prints is the single ultraproduct proof inside
`\ref{sec:transport}`.  Nothing in this file depended on that text, and nothing
in it changed; it is now a Lean-side second route with no printed counterpart
and no badge owed.

This file supplies that explicit bookkeeping.  Every estimate below lives at
one fixed coordinate `n`, is an inequality between real numbers with named
constants, and every proof is finite-dimensional inner-product algebra.  No
ultrafilter, no hyperreal standard part, no compactness extraction and no
sequential limit occurs anywhere in the dependency chain of this module: its
only project import is `GroupApproximation.Sofic.KazhdanCornerMatrices`, whose
transitive import closure contains no hyperreals.

**Operator norm, not Hilbert--Schmidt.**  Section
`\section{Limitations of the operator-norm method}` (`\ref{sec:limits}`)
insists that transport needs operator-norm control -- "Operator-norm control is
needed here to ensure that the classes `[Ad U_n(g)]_ω` are multiplicative;
Hilbert--Schmidt control alone does not provide this" -- and the spectral
estimates below need it for the same reason: `Ad` is not Hilbert--Schmidt
continuous.  That
hypothesis is live in every estimate below.  All operator hypotheses and
conclusions here -- the residual `‖(H - 1) P‖ ≤ δ`, the displacement
`‖(U(g) - 1) P‖`, the leakage `‖(1 - P) Q‖`, and every multiplicative defect
summed by `wordDefect` -- are in the matrix `ℓ²` operator norm of the scoped
instance `Matrix.Norms.L2Operator`, which is the operator norm on the model
Hilbert space; the only Hilbert--Schmidt quantities are the *vectors*
(`‖ξ‖ ≤ M`, `‖(1 - P) ξ‖ ≤ √q`), exactly as in the manuscript's display, since
in the intended instance the model of the almost representation is the adjoint
one and its vectors are the Hilbert--Schmidt vectors `ξ_n` of `x_n`.  Nothing
below is derivable from a Hilbert--Schmidt bound on the microstate defects.

## What is proved here, in the order the appendix uses it

* `sum_norm_act_sub_sq` — the exact energy identity
  `∑_{s ∈ S} ‖U(s)x - x‖² = 2|S| (‖x‖² - ⟪x, H x⟫)`, where `H` is the
  Hermitian average of the microstates over `S` (TeX 1858-1861: "`1 - H_n` is
  the average of the positive operators `1 - Re Ad U_n(ι(s'))`").
* `norm_act_sub_mul_projection_le` — if the residual of `H` on an orthogonal
  projection `P` is at most `δ` in operator norm, then every `s ∈ S` moves
  `ran P` by at most `√(2|S|δ)`.  This is the appendix's
  `½‖(Ad U_n(ι(s')) - 1)η‖² ≤ |S|δ` (TeX 1861) with the constant printed
  and with `P` arbitrary.
* `norm_word_displacement_le` — a word of length `ℓ` in `S` moves `ran P` by
  at most `ℓ√(2|S|δ)` plus the accumulated multiplicative defects along the
  word (`wordDefect`).  This is TeX 1862 verbatim.
* `norm_act_sub_lt_of_eigenvalue_above_gap` — the "too fixed to be moved by
  `κ`" half of the appendix's dichotomy (TeX 1852-1854): a unit eigenvector of
  `H` with eigenvalue above `1 - κ²/(4|S|)` is moved by every `s ∈ S` by
  strictly less than `κ`, at a single coordinate, with no limit.
* `norm_transport_displacement_le`, `transport_bound_sq_le` and
  `transport_bound_le_epsilon` — the appendix's closing computation (TeX
  1903-1936): the three-term decomposition of `T_nξ_n` along `P_n` and `Q_n`,
  and the resulting bound `(qM + 2qM + 2q^{1/2})² ≤ 18q²M² + 16q ≤ ε`.

## What is not proved here

The appendix's robust spectral gap itself — "once the multiplicative defects
of `U_n` on `S` are small enough, no eigenvalue of `H_n` lies in `[a,b]`"
(TeX 1849-1851) — is *not* proved here, and cannot be proved by the
finite-dimensional means of this file.  That statement is about an almost
representation, while Kazhdan's property `(T)` is a statement about exact
unitary representations; the only bridge from one to the other that does not
go through a sum-of-squares certificate for `(T)` is a limit.  The corpus
proves it in `GroupApproximation/Sofic/WeakMFVectorGNS.lean`
(`hermitianAverage_eventually_no_intermediate_eigenvalues`) through a
hyperreal standard part, i.e. through an ultrafilter, and that non-effective
`∃ N` is the only non-explicit input to the estimates below.  For an exact
orthogonal representation the same gap is already proved with no limits at all
by `GroupApproximation.KazhdanEigenvalueBound.eigenvalue_le_of_ne_one`.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace FiniteStageRobustGap

open Matrix
open KazhdanCornerMatrices
open scoped InnerProduct Matrix.Norms.L2Operator

variable {G : Type*} [Group G]

/-! ## Matrices acting on Euclidean space -/

/-- The action of a square matrix on the Euclidean space of its index type. -/
noncomputable def applyMat {Y : FiniteModel} (C : Matrix Y Y ℂ)
    (x : EuclideanSpace ℂ Y) : EuclideanSpace ℂ Y :=
  (Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) C x

theorem applyMat_one {Y : FiniteModel} (x : EuclideanSpace ℂ Y) :
    applyMat (1 : Matrix Y Y ℂ) x = x := by
  simp [applyMat]

theorem applyMat_add {Y : FiniteModel} (C D : Matrix Y Y ℂ)
    (x : EuclideanSpace ℂ Y) :
    applyMat (C + D) x = applyMat C x + applyMat D x := by
  simp [applyMat]

theorem applyMat_sub {Y : FiniteModel} (C D : Matrix Y Y ℂ)
    (x : EuclideanSpace ℂ Y) :
    applyMat (C - D) x = applyMat C x - applyMat D x := by
  simp [applyMat]

theorem applyMat_smul {Y : FiniteModel} (c : ℂ) (C : Matrix Y Y ℂ)
    (x : EuclideanSpace ℂ Y) :
    applyMat (c • C) x = c • applyMat C x := by
  simp [applyMat]

theorem applyMat_mul {Y : FiniteModel} (C D : Matrix Y Y ℂ)
    (x : EuclideanSpace ℂ Y) :
    applyMat (C * D) x = applyMat C (applyMat D x) := by
  unfold applyMat
  rw [map_mul]
  rfl

theorem applyMat_finset_sum {Y : FiniteModel} {ι : Type*} (s : Finset ι)
    (C : ι → Matrix Y Y ℂ) (x : EuclideanSpace ℂ Y) :
    applyMat (∑ i ∈ s, C i) x = ∑ i ∈ s, applyMat (C i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [applyMat]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, applyMat_add, ih]

/-- A matrix coefficient is bounded by the operator norm. -/
theorem norm_applyMat_le {Y : FiniteModel} (C : Matrix Y Y ℂ)
    (x : EuclideanSpace ℂ Y) : ‖applyMat C x‖ ≤ ‖C‖ * ‖x‖ := by
  calc
    ‖applyMat C x‖ ≤
        ‖(Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) C‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖C‖ * ‖x‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM]

/-- The matrix operator norm is characterised by its action on vectors. -/
theorem norm_matrix_le_of_applyMat {Y : FiniteModel} {C : Matrix Y Y ℂ}
    {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : EuclideanSpace ℂ Y, ‖applyMat C x‖ ≤ c * ‖x‖) : ‖C‖ ≤ c := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM C]
  exact ContinuousLinearMap.opNorm_le_bound _ hc h

/-- A unitary matrix acts isometrically. -/
theorem norm_applyMat_of_mem_unitaryGroup {Y : FiniteModel}
    {T : Matrix Y Y ℂ} (hT : T ∈ Matrix.unitaryGroup Y ℂ)
    (x : EuclideanSpace ℂ Y) : ‖applyMat T x‖ = ‖x‖ := by
  let u : unitary (EuclideanSpace ℂ Y →L[ℂ] EuclideanSpace ℂ Y) :=
    ⟨(Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) T,
      Unitary.map_mem (Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) hT⟩
  exact Unitary.norm_map u x

/-! ## Real and complex matrix coefficients -/

/-- On complex Euclidean space the coordinatewise real inner product is the
real part of the complex inner product. -/
theorem real_inner_eq_re {Y : FiniteModel} (x y : EuclideanSpace ℂ Y) :
    inner ℝ x y = (inner ℂ x y).re := by
  simp [PiLp.inner_apply, Complex.inner]

/-- Multiplying by a real scalar commutes with taking the real part. -/
theorem re_ofReal_mul_aux (r : ℝ) (z : ℂ) : ((r : ℂ) * z).re = r * z.re := by
  simp [Complex.mul_re]

/-- The Euclidean operator of a conjugate transpose is the Hilbert adjoint. -/
theorem toEuclideanCLM_conjTranspose {Y : FiniteModel} (C : Matrix Y Y ℂ) :
    (Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) Cᴴ =
      ((Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) C)† := by
  calc
    (Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) Cᴴ =
        (Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) (star C) := by
      rw [Matrix.star_eq_conjTranspose]
    _ = star ((Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) C) :=
      map_star _ C
    _ = ((Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) C)† :=
      ContinuousLinearMap.star_eq_adjoint _

/-- Moving a matrix across the complex inner product transposes it. -/
theorem inner_applyMat_conjTranspose {Y : FiniteModel} (C : Matrix Y Y ℂ)
    (x y : EuclideanSpace ℂ Y) :
    inner ℂ x (applyMat Cᴴ y) = inner ℂ (applyMat C x) y := by
  change inner ℂ x (((Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) Cᴴ) y) =
    inner ℂ (((Matrix.toEuclideanCLM (n := Y) (𝕜 := ℂ)) C) x) y
  rw [toEuclideanCLM_conjTranspose]
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

/-- Moving a matrix across the real inner product transposes it. -/
theorem real_inner_applyMat_conjTranspose {Y : FiniteModel} (C : Matrix Y Y ℂ)
    (x y : EuclideanSpace ℂ Y) :
    inner ℝ (applyMat C x) y = inner ℝ x (applyMat Cᴴ y) := by
  rw [real_inner_eq_re, real_inner_eq_re, inner_applyMat_conjTranspose]

/-- The diagonal coefficient of a conjugate transpose is the conjugate
coefficient. -/
theorem inner_applyMat_conjTranspose_self {Y : FiniteModel}
    (C : Matrix Y Y ℂ) (x : EuclideanSpace ℂ Y) :
    inner ℂ x (applyMat Cᴴ x) = starRingEnd ℂ (inner ℂ x (applyMat C x)) := by
  rw [inner_applyMat_conjTranspose]
  exact (inner_conj_symm (applyMat C x) x).symm

/-- An orthogonal projection matrix is a contraction. -/
theorem norm_applyMat_projection_le {Y : FiniteModel} {P : Matrix Y Y ℂ}
    (hP : IsOrthogonalProjectionMatrix P) (x : EuclideanSpace ℂ Y) :
    ‖applyMat P x‖ ≤ ‖x‖ := by
  have hPP : Pᴴ * P = P := by rw [hP.1, hP.2]
  have hself : ‖applyMat P x‖ ^ 2 = inner ℝ x (applyMat P x) := by
    calc
      ‖applyMat P x‖ ^ 2 = inner ℝ (applyMat P x) (applyMat P x) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = inner ℝ x (applyMat Pᴴ (applyMat P x)) :=
        real_inner_applyMat_conjTranspose P x (applyMat P x)
      _ = inner ℝ x (applyMat (Pᴴ * P) x) := by rw [applyMat_mul]
      _ = inner ℝ x (applyMat P x) := by rw [hPP]
  have hcs : inner ℝ x (applyMat P x) ≤ ‖x‖ * ‖applyMat P x‖ :=
    (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  rcases eq_or_lt_of_le (norm_nonneg (applyMat P x)) with h0 | hpos
  · rw [← h0]
    exact norm_nonneg x
  · refine le_of_mul_le_mul_right ?_ hpos
    calc
      ‖applyMat P x‖ * ‖applyMat P x‖ = ‖applyMat P x‖ ^ 2 := (pow_two _).symm
      _ = inner ℝ x (applyMat P x) := hself
      _ ≤ ‖x‖ * ‖applyMat P x‖ := hcs

/-- An orthogonal projection matrix has operator norm at most one. -/
theorem norm_projection_le_one {Y : FiniteModel} {P : Matrix Y Y ℂ}
    (hP : IsOrthogonalProjectionMatrix P) : ‖P‖ ≤ 1 := by
  refine norm_matrix_le_of_applyMat zero_le_one fun x ↦ ?_
  rw [one_mul]
  exact norm_applyMat_projection_le hP x

/-! ## The finite-stage averaging identity

TeX 1839-1843 and 1858-1862: `H_n` is the Hermitian part of the average
of the microstates over `S`, and `1 - H_n` is the average of the positive
operators `1 - Re Ad U_n(ι(s'))`.  The next three lemmas are that sentence,
as an identity of real numbers at a fixed coordinate. -/

/-- The microstate assigned to `g` acting on the Euclidean model at stage
`n`. -/
noncomputable def act (A : OpAlmostRepresentation G) (n : ℕ) (g : G)
    (x : EuclideanSpace ℂ (A.model n)) : EuclideanSpace ℂ (A.model n) :=
  applyMat (A.map n g : Matrix (A.model n) (A.model n) ℂ) x

@[simp] theorem act_eq_applyMat (A : OpAlmostRepresentation G) (n : ℕ) (g : G)
    (x : EuclideanSpace ℂ (A.model n)) :
    act A n g x =
      applyMat (A.map n g : Matrix (A.model n) (A.model n) ℂ) x := rfl

/-- A finite-stage unitary microstate acts isometrically. -/
theorem norm_act (A : OpAlmostRepresentation G) (n : ℕ) (g : G)
    (x : EuclideanSpace ℂ (A.model n)) : ‖act A n g x‖ = ‖x‖ :=
  norm_applyMat_of_mem_unitaryGroup (A.map n g).2 x

/-- Real matrix coefficient of a microstate at a fixed coordinate. -/
noncomputable def correlation (A : OpAlmostRepresentation G) (n : ℕ)
    (x : EuclideanSpace ℂ (A.model n)) (g : G) : ℝ :=
  inner ℝ x (act A n g x)

@[simp] theorem correlation_eq (A : OpAlmostRepresentation G) (n : ℕ)
    (x : EuclideanSpace ℂ (A.model n)) (g : G) :
    correlation A n x g =
      inner ℝ x (applyMat (A.map n g : Matrix (A.model n) (A.model n) ℂ) x) :=
  rfl

/-- The Hermitian symmetrisation does not change the diagonal coefficient:
`⟪x, H x⟫ = Re ⟪x, M x⟫`. -/
theorem inner_applyMat_hermitianAverage (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) (x : EuclideanSpace ℂ (A.model n)) :
    inner ℂ x (applyMat (hermitianAverage A S n) x) =
      (((inner ℂ x (applyMat (matrixAverage A S n) x)).re : ℝ) : ℂ) := by
  have hsplit : applyMat (hermitianAverage A S n) x =
      (2 : ℂ)⁻¹ • (applyMat (matrixAverage A S n) x +
        applyMat ((matrixAverage A S n)ᴴ) x) := by
    rw [hermitianAverage, applyMat_smul, applyMat_add]
  have hcast :
      ((2 * (inner ℂ x (applyMat (matrixAverage A S n) x)).re : ℝ) : ℂ) =
        2 * (((inner ℂ x (applyMat (matrixAverage A S n) x)).re : ℝ) : ℂ) := by
    norm_cast
  rw [hsplit, inner_smul_right, inner_add_right,
    inner_applyMat_conjTranspose_self, Complex.add_conj, hcast,
    ← mul_assoc, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_mul]

theorem real_inner_applyMat_hermitianAverage (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) (x : EuclideanSpace ℂ (A.model n)) :
    inner ℝ x (applyMat (hermitianAverage A S n) x) =
      inner ℝ x (applyMat (matrixAverage A S n) x) := by
  rw [real_inner_eq_re, real_inner_eq_re, inner_applyMat_hermitianAverage,
    Complex.ofReal_re]

theorem real_inner_applyMat_matrixAverage (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) (x : EuclideanSpace ℂ (A.model n)) :
    inner ℝ x (applyMat (matrixAverage A S n) x) =
      (S.card : ℝ)⁻¹ * ∑ g ∈ S, correlation A n x g := by
  classical
  have hsplit : applyMat (matrixAverage A S n) x =
      ((S.card : ℂ)⁻¹) • ∑ g ∈ S,
        applyMat (A.map n g : Matrix (A.model n) (A.model n) ℂ) x := by
    rw [matrixAverage, applyMat_smul, applyMat_finset_sum]
  have hcoe : ((S.card : ℂ)⁻¹) = (((S.card : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [real_inner_eq_re, hsplit, hcoe, inner_smul_right, re_ofReal_mul_aux,
    inner_sum, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [correlation_eq, real_inner_eq_re]

/-- The sum of the real coefficients over `S` is `|S|` times the diagonal
coefficient of the Hermitian average. -/
theorem sum_correlation_eq_card_mul (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) (hS : S.Nonempty)
    (x : EuclideanSpace ℂ (A.model n)) :
    ∑ g ∈ S, correlation A n x g =
      (S.card : ℝ) * inner ℝ x (applyMat (hermitianAverage A S n) x) := by
  have hcard : (S.card : ℝ) ≠ 0 := by
    have : 0 < S.card := Finset.card_pos.mpr hS
    exact_mod_cast this.ne'
  rw [real_inner_applyMat_hermitianAverage, real_inner_applyMat_matrixAverage,
    ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]

/-! ## The displacement identity and the per-generator estimate -/

/-- Squared displacement of a vector by one microstate. -/
theorem norm_act_sub_sq_eq (A : OpAlmostRepresentation G) (n : ℕ) (g : G)
    (x : EuclideanSpace ℂ (A.model n)) :
    ‖act A n g x - x‖ ^ 2 = 2 * ‖x‖ ^ 2 - 2 * correlation A n x g := by
  have h := norm_sub_sq_real (act A n g x) x
  rw [norm_act] at h
  rw [h, real_inner_comm x (act A n g x)]
  rw [correlation]
  ring

/-- **The energy identity.**  `∑_{s ∈ S} ‖U(s)x - x‖² = 2|S|(‖x‖² - ⟪x,Hx⟫)`;
TeX 1858-1861. -/
theorem sum_norm_act_sub_sq (A : OpAlmostRepresentation G) (S : Finset G)
    (n : ℕ) (hS : S.Nonempty) (x : EuclideanSpace ℂ (A.model n)) :
    ∑ g ∈ S, ‖act A n g x - x‖ ^ 2 =
      2 * (S.card : ℝ) *
        (‖x‖ ^ 2 - inner ℝ x (applyMat (hermitianAverage A S n) x)) := by
  classical
  have hsum : ∑ g ∈ S, ‖act A n g x - x‖ ^ 2 =
      ∑ g ∈ S, (2 * ‖x‖ ^ 2 - 2 * correlation A n x g) :=
    Finset.sum_congr rfl fun g _ ↦ norm_act_sub_sq_eq A n g x
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum,
    nsmul_eq_mul, sum_correlation_eq_card_mul A S n hS x]
  ring

/-- **Per-generator displacement.**  Each single generator displacement is
bounded by the total energy; TeX 1861. -/
theorem norm_act_sub_sq_le (A : OpAlmostRepresentation G) (S : Finset G)
    (n : ℕ) (hS : S.Nonempty) (x : EuclideanSpace ℂ (A.model n)) {g : G}
    (hg : g ∈ S) :
    ‖act A n g x - x‖ ^ 2 ≤
      2 * (S.card : ℝ) *
        (‖x‖ ^ 2 - inner ℝ x (applyMat (hermitianAverage A S n) x)) := by
  classical
  rw [← sum_norm_act_sub_sq A S n hS x]
  exact Finset.single_le_sum
    (f := fun g : G ↦ ‖act A n g x - x‖ ^ 2) (fun i _ ↦ sq_nonneg _) hg

/-- Cauchy–Schwarz turns the residual of `H` into an energy bound. -/
theorem energy_le_norm_mul {Y : FiniteModel} (H : Matrix Y Y ℂ)
    (x : EuclideanSpace ℂ Y) :
    ‖x‖ ^ 2 - inner ℝ x (applyMat H x) ≤ ‖x - applyMat H x‖ * ‖x‖ := by
  have h1 : ‖x‖ ^ 2 - inner ℝ x (applyMat H x) =
      inner ℝ x (x - applyMat H x) := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
  rw [h1]
  calc
    inner ℝ x (x - applyMat H x) ≤ |inner ℝ x (x - applyMat H x)| :=
      le_abs_self _
    _ ≤ ‖x‖ * ‖x - applyMat H x‖ := abs_real_inner_le_norm _ _
    _ = ‖x - applyMat H x‖ * ‖x‖ := mul_comm _ _

/-! ## The appendix's estimate (i): displacement of a spectral corner

TeX 1847-1864.  Granted the residual bound `‖(H_n - 1)P_n‖ ≤ δ`, every
generator moves the corner by at most `√(2|S|δ)` in operator norm, with the
constant printed by the manuscript. -/

/-- **Generator displacement of a projection corner, explicit constant.**
If `‖(H - 1)P‖ ≤ δ` then `‖(U(g) - 1)P‖ ≤ √(2|S|δ)` for every `g ∈ S`.

Neither hypothesis is a standing assumption: both are discharged in the
corpus for the manuscript's `P_n = spectralAbove H_n θ`.  `hP` is
`KazhdanCornerMatrices.spectralAbove_isOrthogonalProjection`; `hres` is
`KazhdanCornerMatrices.norm_sub_one_mul_spectralAbove_le` (from the eigenvalue
band, ultrafilter-free) and, for the manuscript's `∃ N` form,
`KazhdanCornerMatrices.hermitianAverage_eventually_top_spectral_residual`.
This lemma is the quantitative single-stage replacement for
`KazhdanCornerMatrices.topSpectralDisplacement_vanishing`, which states the
same fact with the constant erased into an `∃ N`. -/
theorem norm_act_sub_mul_projection_le (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) (hS : S.Nonempty)
    {P : Matrix (A.model n) (A.model n) ℂ}
    (hP : IsOrthogonalProjectionMatrix P) {δ : ℝ} (hδ : 0 ≤ δ)
    (hres : ‖(hermitianAverage A S n - 1) * P‖ ≤ δ) {g : G} (hg : g ∈ S) :
    ‖((A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1) * P‖ ≤
      Real.sqrt (2 * (S.card : ℝ) * δ) := by
  have hcard : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hc0 : 0 ≤ 2 * (S.card : ℝ) * δ := by
    have : (0 : ℝ) ≤ 2 * (S.card : ℝ) := by linarith
    exact mul_nonneg this hδ
  refine norm_matrix_le_of_applyMat (Real.sqrt_nonneg _) fun ξ ↦ ?_
  have hηnorm : ‖applyMat P ξ‖ ≤ ‖ξ‖ := norm_applyMat_projection_le hP ξ
  have hexpand :
      applyMat (((A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1) * P) ξ =
        act A n g (applyMat P ξ) - applyMat P ξ := by
    rw [applyMat_mul, applyMat_sub, applyMat_one, act_eq_applyMat]
  have hresvec :
      ‖applyMat P ξ -
        applyMat (hermitianAverage A S n) (applyMat P ξ)‖ ≤ δ * ‖ξ‖ := by
    have h1 : applyMat P ξ -
        applyMat (hermitianAverage A S n) (applyMat P ξ) =
          applyMat ((1 - hermitianAverage A S n) * P) ξ := by
      rw [applyMat_mul, applyMat_sub, applyMat_one]
    have h2 : ‖(1 - hermitianAverage A S n) * P‖ =
        ‖(hermitianAverage A S n - 1) * P‖ := by
      rw [show (1 - hermitianAverage A S n) * P =
        -((hermitianAverage A S n - 1) * P) by noncomm_ring, norm_neg]
    calc
      ‖applyMat P ξ -
          applyMat (hermitianAverage A S n) (applyMat P ξ)‖ =
          ‖applyMat ((1 - hermitianAverage A S n) * P) ξ‖ := by rw [h1]
      _ ≤ ‖(1 - hermitianAverage A S n) * P‖ * ‖ξ‖ := norm_applyMat_le _ _
      _ ≤ δ * ‖ξ‖ := by
        rw [h2]
        exact mul_le_mul_of_nonneg_right hres (norm_nonneg _)
  have henergy : ‖applyMat P ξ‖ ^ 2 -
      inner ℝ (applyMat P ξ)
        (applyMat (hermitianAverage A S n) (applyMat P ξ)) ≤
      δ * ‖ξ‖ ^ 2 := by
    calc
      ‖applyMat P ξ‖ ^ 2 -
          inner ℝ (applyMat P ξ)
            (applyMat (hermitianAverage A S n) (applyMat P ξ)) ≤
          ‖applyMat P ξ -
            applyMat (hermitianAverage A S n) (applyMat P ξ)‖ *
              ‖applyMat P ξ‖ :=
        energy_le_norm_mul (hermitianAverage A S n) (applyMat P ξ)
      _ ≤ (δ * ‖ξ‖) * ‖ξ‖ :=
        mul_le_mul hresvec hηnorm (norm_nonneg _)
          (mul_nonneg hδ (norm_nonneg _))
      _ = δ * ‖ξ‖ ^ 2 := by ring
  have hsq : ‖act A n g (applyMat P ξ) - applyMat P ξ‖ ^ 2 ≤
      (2 * (S.card : ℝ) * δ) * ‖ξ‖ ^ 2 := by
    calc
      ‖act A n g (applyMat P ξ) - applyMat P ξ‖ ^ 2 ≤
          2 * (S.card : ℝ) *
            (‖applyMat P ξ‖ ^ 2 -
              inner ℝ (applyMat P ξ)
                (applyMat (hermitianAverage A S n) (applyMat P ξ))) :=
        norm_act_sub_sq_le A S n hS (applyMat P ξ) hg
      _ ≤ 2 * (S.card : ℝ) * (δ * ‖ξ‖ ^ 2) := by
        have h2card : (0 : ℝ) ≤ 2 * (S.card : ℝ) := by linarith
        exact mul_le_mul_of_nonneg_left henergy h2card
      _ = (2 * (S.card : ℝ) * δ) * ‖ξ‖ ^ 2 := by ring
  rw [hexpand]
  have hrhs : 0 ≤ Real.sqrt (2 * (S.card : ℝ) * δ) * ‖ξ‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  refine (sq_le_sq₀ (norm_nonneg _) hrhs).1 ?_
  calc
    ‖act A n g (applyMat P ξ) - applyMat P ξ‖ ^ 2 ≤
        (2 * (S.card : ℝ) * δ) * ‖ξ‖ ^ 2 := hsq
    _ = (Real.sqrt (2 * (S.card : ℝ) * δ) * ‖ξ‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc0]

/-! ## Words: TeX 1862

"a word in `S` of length `ℓ` moves `η` by at most `ℓ√(2|S|δ)` plus the
accumulated multiplicative defects". -/

/-- The accumulated multiplicative defect of a word, read left to right.  The
empty word contributes the identity defect `‖U(1) - 1‖`, which is the defect
incurred by the microstate at the empty product. -/
noncomputable def wordDefect (A : OpAlmostRepresentation G) (n : ℕ) :
    List G → ℝ
  | [] => ‖(A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1‖
  | g :: L =>
      ‖(A.map n (g * L.prod) : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
            (A.map n L.prod : Matrix (A.model n) (A.model n) ℂ)‖ +
        wordDefect A n L

theorem wordDefect_nonneg (A : OpAlmostRepresentation G) (n : ℕ)
    (L : List G) : 0 ≤ wordDefect A n L := by
  induction L with
  | nil => exact norm_nonneg _
  | cons g L ih =>
      exact add_nonneg (norm_nonneg _) ih

/-- **Word displacement.**  Generator control propagates along a word at
linear cost, plus the accumulated multiplicative defects. -/
theorem norm_prod_sub_one_mul_le (A : OpAlmostRepresentation G) (n : ℕ)
    {P : Matrix (A.model n) (A.model n) ℂ} (hPnorm : ‖P‖ ≤ 1) {c : ℝ}
    (L : List G)
    (hL : ∀ g ∈ L,
      ‖((A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1) * P‖ ≤ c) :
    ‖((A.map n L.prod : Matrix (A.model n) (A.model n) ℂ) - 1) * P‖ ≤
      (L.length : ℝ) * c + wordDefect A n L := by
  letI : Nonempty (A.model n) := Fintype.card_pos_iff.mp (A.modelNonempty n)
  induction L with
  | nil =>
      have hgoal :
          ‖((A.map n (([] : List G).prod) :
              Matrix (A.model n) (A.model n) ℂ) - 1) * P‖ ≤
            ‖(A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1‖ := by
        rw [List.prod_nil]
        calc
          ‖((A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1) * P‖ ≤
              ‖(A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1‖ * ‖P‖ :=
            Matrix.l2_opNorm_mul _ _
          _ ≤ ‖(A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1‖ * 1 :=
            mul_le_mul_of_nonneg_left hPnorm (norm_nonneg _)
          _ = ‖(A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1‖ := mul_one _
      simpa [wordDefect] using hgoal
  | cons g L ih =>
      have hIH :
          ‖((A.map n L.prod : Matrix (A.model n) (A.model n) ℂ) - 1) * P‖ ≤
            (L.length : ℝ) * c + wordDefect A n L :=
        ih fun k hk ↦ hL k (List.mem_cons_of_mem g hk)
      have hgen :
          ‖((A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1) * P‖ ≤ c :=
        hL g (by simp)
      have hunit : ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ)‖ = 1 :=
        CStarRing.norm_of_mem_unitary (A.map n g).2
      have hdecomp :
          ((A.map n (g * L.prod) : Matrix (A.model n) (A.model n) ℂ) - 1) * P =
            ((A.map n (g * L.prod) : Matrix (A.model n) (A.model n) ℂ) -
                (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
                  (A.map n L.prod : Matrix (A.model n) (A.model n) ℂ)) * P +
              ((A.map n g : Matrix (A.model n) (A.model n) ℂ) *
                  (((A.map n L.prod :
                      Matrix (A.model n) (A.model n) ℂ) - 1) * P) +
                ((A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1) * P) := by
        noncomm_ring
      have hdefect :
          ‖((A.map n (g * L.prod) : Matrix (A.model n) (A.model n) ℂ) -
              (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
                (A.map n L.prod : Matrix (A.model n) (A.model n) ℂ)) * P‖ ≤
            ‖(A.map n (g * L.prod) : Matrix (A.model n) (A.model n) ℂ) -
              (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
                (A.map n L.prod : Matrix (A.model n) (A.model n) ℂ)‖ := by
        calc
          ‖((A.map n (g * L.prod) : Matrix (A.model n) (A.model n) ℂ) -
              (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
                (A.map n L.prod : Matrix (A.model n) (A.model n) ℂ)) * P‖ ≤
              ‖(A.map n (g * L.prod) : Matrix (A.model n) (A.model n) ℂ) -
                (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
                  (A.map n L.prod :
                    Matrix (A.model n) (A.model n) ℂ)‖ * ‖P‖ :=
            Matrix.l2_opNorm_mul _ _
          _ ≤ ‖(A.map n (g * L.prod) : Matrix (A.model n) (A.model n) ℂ) -
                (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
                  (A.map n L.prod :
                    Matrix (A.model n) (A.model n) ℂ)‖ * 1 :=
            mul_le_mul_of_nonneg_left hPnorm (norm_nonneg _)
          _ = ‖(A.map n (g * L.prod) : Matrix (A.model n) (A.model n) ℂ) -
                (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
                  (A.map n L.prod : Matrix (A.model n) (A.model n) ℂ)‖ :=
            mul_one _
      have hmiddle :
          ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ) *
              (((A.map n L.prod :
                Matrix (A.model n) (A.model n) ℂ) - 1) * P)‖ ≤
            (L.length : ℝ) * c + wordDefect A n L := by
        calc
          ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ) *
              (((A.map n L.prod :
                Matrix (A.model n) (A.model n) ℂ) - 1) * P)‖ ≤
              ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ)‖ *
                ‖((A.map n L.prod :
                  Matrix (A.model n) (A.model n) ℂ) - 1) * P‖ :=
            Matrix.l2_opNorm_mul _ _
          _ = ‖((A.map n L.prod :
                Matrix (A.model n) (A.model n) ℂ) - 1) * P‖ := by
            rw [hunit, one_mul]
          _ ≤ (L.length : ℝ) * c + wordDefect A n L := hIH
      have hsum :
          ‖((A.map n ((g :: L).prod) :
              Matrix (A.model n) (A.model n) ℂ) - 1) * P‖ ≤
            (‖(A.map n (g * L.prod) : Matrix (A.model n) (A.model n) ℂ) -
                (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
                  (A.map n L.prod : Matrix (A.model n) (A.model n) ℂ)‖) +
              (((L.length : ℝ) * c + wordDefect A n L) + c) := by
        rw [List.prod_cons, hdecomp]
        refine (norm_add_le _ _).trans (add_le_add hdefect ?_)
        exact (norm_add_le _ _).trans (add_le_add hmiddle hgen)
      have hlen : (((g :: L).length : ℕ) : ℝ) = (L.length : ℝ) + 1 := by
        simp
      rw [hlen]
      simp only [wordDefect]
      linarith

/-- **The appendix's word estimate, TeX 1862.**  A word of length `ℓ` in
`S` moves the corner `P` by at most `ℓ√(2|S|δ)` plus the accumulated
multiplicative defects along the word. -/
theorem norm_word_displacement_le (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) (hS : S.Nonempty)
    {P : Matrix (A.model n) (A.model n) ℂ}
    (hP : IsOrthogonalProjectionMatrix P) {δ : ℝ} (hδ : 0 ≤ δ)
    (hres : ‖(hermitianAverage A S n - 1) * P‖ ≤ δ) (L : List G)
    (hLS : ∀ g ∈ L, g ∈ S) :
    ‖((A.map n L.prod : Matrix (A.model n) (A.model n) ℂ) - 1) * P‖ ≤
      (L.length : ℝ) * Real.sqrt (2 * (S.card : ℝ) * δ) +
        wordDefect A n L :=
  norm_prod_sub_one_mul_le A n (norm_projection_le_one hP) L
    fun g hg ↦
      norm_act_sub_mul_projection_le A S n hS hP hδ hres (hLS g hg)

/-! ## The dichotomy of TeX 1852-1854, finite-stage half

"an eigenvector with intermediate eigenvalue would be a unit vector that the
Kazhdan pair forbids: too fixed to be moved by `κ`, too moved to be fixed."
The first half is an unconditional estimate at a single coordinate and is
proved here.  The second half is a statement about exact representations; see
`GroupApproximation.KazhdanEigenvalueBound.eigenvalue_le_of_ne_one`. -/

/-- The diagonal coefficient of an eigenvector is its eigenvalue. -/
theorem inner_eigenvector_eq (A : OpAlmostRepresentation G) (S : Finset G)
    (n : ℕ) {x : EuclideanSpace ℂ (A.model n)} (hx : ‖x‖ = 1) {lam : ℝ}
    (heig : applyMat (hermitianAverage A S n) x = (lam : ℂ) • x) :
    inner ℝ x (applyMat (hermitianAverage A S n) x) = lam := by
  rw [heig, real_inner_eq_re, inner_smul_right, re_ofReal_mul_aux,
    ← real_inner_eq_re, real_inner_self_eq_norm_sq, hx]
  ring

/-- **Too fixed to be moved.**  A unit eigenvector of the Hermitian average
with eigenvalue `lam` is displaced by each `g ∈ S` by at most
`√(2|S|(1 - lam))`; no limit is used. -/
theorem norm_act_sub_sq_le_of_eigenvector (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) (hS : S.Nonempty)
    {x : EuclideanSpace ℂ (A.model n)} (hx : ‖x‖ = 1) {lam : ℝ}
    (heig : applyMat (hermitianAverage A S n) x = (lam : ℂ) • x) {g : G}
    (hg : g ∈ S) :
    ‖act A n g x - x‖ ^ 2 ≤ 2 * (S.card : ℝ) * (1 - lam) := by
  have h := norm_act_sub_sq_le A S n hS x hg
  rw [inner_eigenvector_eq A S n hx heig, hx] at h
  have hone : (1 : ℝ) ^ 2 = 1 := one_pow 2
  rw [hone] at h
  exact h

/-- **The `κ`-form of the dichotomy's first half, TeX 1852-1854.**  If the
eigenvalue exceeds the Kazhdan moving-spectrum bound `1 - κ²/(4|S|)`, then the
eigenvector is moved by every generator by strictly less than `κ`: it is too
fixed for the Kazhdan pair.  (The sharper constant `κ/√2` follows from
`norm_act_sub_sq_le_of_eigenvector` in the same way.) -/
theorem norm_act_sub_lt_of_eigenvalue_above_gap (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) (hS : S.Nonempty)
    {x : EuclideanSpace ℂ (A.model n)} (hx : ‖x‖ = 1) {lam kappa : ℝ}
    (hkappa : 0 < kappa)
    (heig : applyMat (hermitianAverage A S n) x = (lam : ℂ) • x)
    (hlam : 1 - kappa ^ 2 / (4 * (S.card : ℝ)) < lam) {g : G} (hg : g ∈ S) :
    ‖act A n g x - x‖ < kappa := by
  have hcard : (0 : ℝ) < (S.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hS
  have hsq : ‖act A n g x - x‖ ^ 2 ≤ 2 * (S.card : ℝ) * (1 - lam) :=
    norm_act_sub_sq_le_of_eigenvector A S n hS hx heig hg
  have hc4 : (0 : ℝ) < 4 * (S.card : ℝ) := by linarith
  have hmul : (1 - lam) * (4 * (S.card : ℝ)) < kappa ^ 2 :=
    (lt_div_iff₀ hc4).mp (by linarith)
  by_contra hcon
  push Not at hcon
  have hkk : kappa * kappa ≤ ‖act A n g x - x‖ * ‖act A n g x - x‖ :=
    mul_le_mul hcon hcon hkappa.le (norm_nonneg _)
  nlinarith [hkk, hsq, hmul, sq_nonneg kappa]

/-! ## The appendix's closing computation, TeX 1903-1936 -/

/-- **Combining the estimates.**  With `Q = T P T*` for a unitary `T`, the
three-term decomposition `Tξ = PQTξ + (1-P)QTξ + (1-Q)Tξ` and the three
tolerances `‖(1-P)ξ‖ ≤ √q`, `‖(1-P)Q‖ ≤ q`, `‖D P‖ ≤ q` give the manuscript's
bound `qM + 2qM + 2q^{1/2}` for `‖D T ξ‖`, where `D = A_n - 1` has operator
norm at most `2` and `‖ξ‖ ≤ M`.

The three tolerances are the manuscript's own display and are discharged in
the corpus, not assumed here: `hleak` by
`KazhdanCompressorCorner.one_sub_corner_mul_moved_vanishing` (the equal-rank
flip -- note that this lemma, not the present one, is where rank enters, so
no dimension count occurs below), `hdisp` by
`KazhdanCornerMatrices.topSpectralDisplacement_vanishing_of_generates`,
`hconc` by the spectral-capture bound of `Sofic/SpectralCapture.lean`, and
`hQT`/`hQproj` by `KazhdanCompressorCorner.movedProjection` together with
`KazhdanCornerMatrices.unitary_conjugate_isOrthogonalProjection`. -/
theorem norm_transport_displacement_le {Y : FiniteModel}
    {P Q T D : Matrix Y Y ℂ} {ξ : EuclideanSpace ℂ Y} {q M : ℝ}
    (hQproj : IsOrthogonalProjectionMatrix Q)
    (hT : T ∈ Matrix.unitaryGroup Y ℂ) (hQT : Q = T * P * Tᴴ) (hq : 0 ≤ q)
    (hconc : ‖applyMat (1 - P) ξ‖ ≤ Real.sqrt q)
    (hleak : ‖(1 - P) * Q‖ ≤ q) (hdisp : ‖D * P‖ ≤ q) (hD : ‖D‖ ≤ 2)
    (hξ : ‖ξ‖ ≤ M) :
    ‖applyMat D (applyMat T ξ)‖ ≤ q * M + 2 * (q * M) + 2 * Real.sqrt q := by
  have hTξ : ‖applyMat T ξ‖ = ‖ξ‖ := norm_applyMat_of_mem_unitaryGroup hT ξ
  have hTξle : ‖applyMat T ξ‖ ≤ M := by rw [hTξ]; exact hξ
  have hsplit : applyMat D (applyMat T ξ) =
      applyMat (D * (P * Q)) (applyMat T ξ) +
        applyMat (D * ((1 - P) * Q)) (applyMat T ξ) +
          applyMat (D * (1 - Q)) (applyMat T ξ) := by
    have hid : D = D * (P * Q) + D * ((1 - P) * Q) + D * (1 - Q) := by
      noncomm_ring
    calc
      applyMat D (applyMat T ξ) =
          applyMat (D * (P * Q) + D * ((1 - P) * Q) + D * (1 - Q))
            (applyMat T ξ) := by rw [← hid]
      _ = applyMat (D * (P * Q)) (applyMat T ξ) +
            applyMat (D * ((1 - P) * Q)) (applyMat T ξ) +
              applyMat (D * (1 - Q)) (applyMat T ξ) := by
        rw [applyMat_add, applyMat_add]
  have h1 : ‖applyMat (D * (P * Q)) (applyMat T ξ)‖ ≤ q * M := by
    have hassoc : D * (P * Q) = (D * P) * Q := by noncomm_ring
    have hQle : ‖applyMat Q (applyMat T ξ)‖ ≤ M :=
      (norm_applyMat_projection_le hQproj (applyMat T ξ)).trans hTξle
    calc
      ‖applyMat (D * (P * Q)) (applyMat T ξ)‖ =
          ‖applyMat (D * P) (applyMat Q (applyMat T ξ))‖ := by
        rw [hassoc, applyMat_mul]
      _ ≤ ‖D * P‖ * ‖applyMat Q (applyMat T ξ)‖ := norm_applyMat_le _ _
      _ ≤ q * M := mul_le_mul hdisp hQle (norm_nonneg _) hq
  have h2 : ‖applyMat (D * ((1 - P) * Q)) (applyMat T ξ)‖ ≤ 2 * (q * M) := by
    have hinner : ‖D * ((1 - P) * Q)‖ ≤ 2 * q := by
      calc
        ‖D * ((1 - P) * Q)‖ ≤ ‖D‖ * ‖(1 - P) * Q‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ 2 * q := mul_le_mul hD hleak (norm_nonneg _) (by norm_num)
    calc
      ‖applyMat (D * ((1 - P) * Q)) (applyMat T ξ)‖ ≤
          ‖D * ((1 - P) * Q)‖ * ‖applyMat T ξ‖ := norm_applyMat_le _ _
      _ ≤ (2 * q) * M :=
        mul_le_mul hinner hTξle (norm_nonneg _) (by linarith)
      _ = 2 * (q * M) := by ring
  have h3 : ‖applyMat (D * (1 - Q)) (applyMat T ξ)‖ ≤ 2 * Real.sqrt q := by
    have hTT : Tᴴ * T = 1 := by
      have h := hT
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
      exact h
    have hcomm : (1 - Q) * T = T * (1 - P) := by
      calc
        (1 - Q) * T = T - (T * P * Tᴴ) * T := by
          rw [hQT]
          noncomm_ring
        _ = T - T * P * (Tᴴ * T) := by noncomm_ring
        _ = T * (1 - P) := by
          rw [hTT]
          noncomm_ring
    have hvec : applyMat (1 - Q) (applyMat T ξ) =
        applyMat T (applyMat (1 - P) ξ) := by
      rw [← applyMat_mul, ← applyMat_mul, hcomm]
    calc
      ‖applyMat (D * (1 - Q)) (applyMat T ξ)‖ =
          ‖applyMat D (applyMat (1 - Q) (applyMat T ξ))‖ := by
        rw [applyMat_mul]
      _ = ‖applyMat D (applyMat T (applyMat (1 - P) ξ))‖ := by rw [hvec]
      _ ≤ ‖D‖ * ‖applyMat T (applyMat (1 - P) ξ)‖ := norm_applyMat_le _ _
      _ = ‖D‖ * ‖applyMat (1 - P) ξ‖ := by
        rw [norm_applyMat_of_mem_unitaryGroup hT]
      _ ≤ 2 * Real.sqrt q :=
        mul_le_mul hD hconc (norm_nonneg _) (by norm_num)
  rw [hsplit]
  calc
    ‖applyMat (D * (P * Q)) (applyMat T ξ) +
        applyMat (D * ((1 - P) * Q)) (applyMat T ξ) +
          applyMat (D * (1 - Q)) (applyMat T ξ)‖ ≤
        ‖applyMat (D * (P * Q)) (applyMat T ξ) +
          applyMat (D * ((1 - P) * Q)) (applyMat T ξ)‖ +
            ‖applyMat (D * (1 - Q)) (applyMat T ξ)‖ := norm_add_le _ _
    _ ≤ (‖applyMat (D * (P * Q)) (applyMat T ξ)‖ +
          ‖applyMat (D * ((1 - P) * Q)) (applyMat T ξ)‖) +
            ‖applyMat (D * (1 - Q)) (applyMat T ξ)‖ :=
      by
        have hab := norm_add_le (applyMat (D * (P * Q)) (applyMat T ξ))
          (applyMat (D * ((1 - P) * Q)) (applyMat T ξ))
        linarith
    _ ≤ (q * M + 2 * (q * M)) + 2 * Real.sqrt q :=
      add_le_add (add_le_add h1 h2) h3

/-- The squared form of the manuscript's display:
`(qM + 2qM + 2q^{1/2})² ≤ 18q²M² + 16q`. -/
theorem transport_bound_sq_le {q M : ℝ} (hq : 0 ≤ q) :
    (q * M + 2 * (q * M) + 2 * Real.sqrt q) ^ 2 ≤
      18 * q ^ 2 * M ^ 2 + 16 * q := by
  have hs : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  nlinarith [Real.sqrt_nonneg q, hs, hq,
    sq_nonneg (3 * q * M - 2 * Real.sqrt q)]

/-- The manuscript's choice of tolerance closes the estimate: with
`q ≤ 1` and `q · 40(M² + 1) ≤ ε` — which is exactly
`q = min(1, ε/(40(M²+1)))` — the bound `18q²M² + 16q` is at most `ε`. -/
theorem transport_bound_le_epsilon {ε M q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hqε : q * (40 * (M ^ 2 + 1)) ≤ ε) :
    18 * q ^ 2 * M ^ 2 + 16 * q ≤ ε := by
  nlinarith [mul_nonneg (mul_nonneg hq (sub_nonneg.mpr hq1)) (sq_nonneg M),
    mul_nonneg hq (sq_nonneg M), hq, sq_nonneg M]

end FiniteStageRobustGap
end GroupApproximation
