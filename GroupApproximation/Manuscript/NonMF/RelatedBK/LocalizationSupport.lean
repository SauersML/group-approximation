import GroupApproximation.Manuscript.NonMF.RelatedBK.LocalizationMatrixNorms
import GroupApproximation.Analysis.NormMatrixCorona
import GroupApproximation.Analysis.CStarExactness
import GroupApproximation.Analysis.CStarCompletelyPositiveForm
import GroupApproximation.Analysis.CStarCPStarTarget
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work (Blackadar--Kirchberg): vector states support a CP map killing the tail ideal

Census row `14ee41b7f3cc`, `non_mf_groups_exist.tex` L310 (Related work):

> Their 1997 paper developed these notions and proved that a separable
> $C^*$-algebra is NF if and only if it is nuclear and MF~\cite{BK}.

This module proves the Hahn--Banach support inequality behind the localization step of
`CoronaUCPFiniteCoordinateLocalizationStatement`.

## Setting

* `Φ : ∏ M_{X n} → M_Z` is completely positive, and `Φ x = 0` whenever `x n = 0` for `n ≥ N`.
* `T` is a finite set of bounded matrix sequences.
* A *vector state at coordinate `n`* is a vector `ξ : Z × X n → ℂ`. Its test values are
  `z(i, j, t) = ∑_{a,b} conj ξ(i,a) · t_n(a,b) · ξ(j,b)`.
* The target point is `Φ̂(i, j, t) = Φ(t)_{ij}`.

## Statement

`localization_support` shows that every complex functional `f` on `ℂ^{Z × Z × T}` satisfies
`Re f(Φ̂) < Re f(z) + δ` for some vector state `z` at a coordinate `n ≥ N`.

## Proof

Suppose not. Write `f(z) = ∑ c_p z_p`, and put `h_{ij} = ∑_t c(i,j,t) t` in `∏ M_{X n}`.

1. The vector states at coordinate `n` form a cone of the form
   `ξ ↦ ⟨ξ, H_n ξ⟩`, where `H_n` is the matrix with blocks `h_{ij}(n)`. The failure of the
   inequality, applied along real rescalings of `ξ`, forces `Re ⟨ξ, H_n ξ⟩ ≤ 0`. Applied at
   `ξ = 0`, it forces `δ ≤ Re f(Φ̂)`.
2. So `-(H_n + H_nᴴ) = G_nᴴ G_n` for every `n ≥ N`. The blocks of `G_n` are uniformly bounded,
   so they assemble into a matrix `Nm` over `∏ M_{X n}` whose Gram matrix agrees with
   `-(h_{ij} + h_{ji}^*)` on the tail `n ≥ N`.
3. Since `Φ` kills the tail ideal and preserves adjoints, complete positivity gives
   `-(Φ(h_{ij}) + Φ(h_{ji})^*) = P^* P` entrywise. Evaluating the `(i, j)` entry at the
   `(i, j)` matrix coordinate and summing gives `0 ≤ -2 Re f(Φ̂)`. That contradicts step 1.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedBK

open GroupApproximation.CStarExactness
open scoped Matrix Matrix.Norms.L2Operator ENNReal

noncomputable section

/-- Bounded matrix sequences form a C-star algebra. -/
local instance boundedMatrixSequenceCStarAlgebraForLocalizationSupport
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] :
    CStarAlgebra (BoundedMatrixSequence (fun n ↦ X n)) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := by
    constructor
    intro c x
    apply lp.ext
    funext n
    change star (c • x n) = star c • star (x n)
    rw [star_smul]

/-- Matrix blocks at the scoped operator norm are C-star algebras. -/
local instance matrixBlockCStarAlgebraForLocalizationSupport
    (Z : Type) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- The test values of a vector `ξ` at coordinate `n` against the finite set `T`. -/
def localizationVectorState (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] {Z : Type}
    (T : Finset (BoundedMatrixSequence (fun n ↦ X n))) {n : ℕ} (ξ : Z × X n → ℂ) :
    Z × Z × T → ℂ :=
  fun p ↦ ∑ a : X n, ∑ b : X n,
    star (ξ (p.1, a)) * ((p.2.2 : BoundedMatrixSequence (fun n ↦ X n)) n) a b * ξ (p.2.1, b)

/-- The vector states at coordinates `n ≥ N`. -/
def localizationVectorStateSet (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] (Z : Type)
    (T : Finset (BoundedMatrixSequence (fun n ↦ X n))) (N : ℕ) : Set (Z × Z × T → ℂ) :=
  {z | ∃ n, N ≤ n ∧ ∃ ξ : Z × X n → ℂ, z = localizationVectorState X T ξ}

/-- The target point `(i, j, t) ↦ Φ(t)_{ij}`. -/
def localizationTarget (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] {Z : Type}
    (T : Finset (BoundedMatrixSequence (fun n ↦ X n)))
    (Φ : BoundedMatrixSequence (fun n ↦ X n) →ₗ[ℂ] Matrix Z Z ℂ) : Z × Z × T → ℂ :=
  fun p ↦ Φ (p.2.2 : BoundedMatrixSequence (fun n ↦ X n)) p.1 p.2.1

/-- The coefficient sequence `h_{ij} = ∑_t c(i,j,t) t`. -/
def localizationCoeff (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] {Z : Type}
    (T : Finset (BoundedMatrixSequence (fun n ↦ X n))) (c : Z × Z × T → ℂ) (i j : Z) :
    BoundedMatrixSequence (fun n ↦ X n) :=
  ∑ t : T, c (i, j, t) • (t : BoundedMatrixSequence (fun n ↦ X n))

theorem localizationCoeff_apply (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] {Z : Type}
    (T : Finset (BoundedMatrixSequence (fun n ↦ X n))) (c : Z × Z × T → ℂ) (i j : Z)
    (n : ℕ) (a b : X n) :
    localizationCoeff X T c i j n a b =
      ∑ t : T, c (i, j, t) * (t : BoundedMatrixSequence (fun n ↦ X n)) n a b := by
  rw [localizationCoeff, lp.coeFn_sum, Finset.sum_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [lp.coeFn_smul, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]

/-- The quadratic-form matrix `H_n` with blocks `h_{ij}(n)`. -/
def localizationQuadMatrix (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] {Z : Type}
    (T : Finset (BoundedMatrixSequence (fun n ↦ X n))) (c : Z × Z × T → ℂ) (n : ℕ) :
    Matrix (Z × X n) (Z × X n) ℂ :=
  Matrix.of fun P Q ↦ localizationCoeff X T c P.1 Q.1 n P.2 Q.2

theorem localizationBlockEntry_quadMatrix (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    {Z : Type} (T : Finset (BoundedMatrixSequence (fun n ↦ X n))) (c : Z × Z × T → ℂ)
    (n : ℕ) (i j : Z) :
    localizationBlockEntry (localizationQuadMatrix X T c n) i j = localizationCoeff X T c i j n := by
  ext a b
  rfl

/-- A complex functional on a finite coordinate space has coefficients. -/
theorem localization_exists_coeff {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℂ) →L[ℂ] ℂ) : ∃ c : ι → ℂ, ∀ z, f z = ∑ p, c p * z p :=
  ⟨fun p ↦ f fun j ↦ if p = j then 1 else 0, fun z ↦
    (LinearMap.pi_apply_eq_sum_univ (f : (ι → ℂ) →ₗ[ℂ] ℂ) z).trans
      (Finset.sum_congr rfl fun p _ ↦ (smul_eq_mul _ _).trans (mul_comm _ _))⟩

/-- Pairing coefficients with a vector state is the quadratic form of `H_n`. -/
theorem localization_sum_coeff_vectorState (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    {Z : Type} [Fintype Z] (T : Finset (BoundedMatrixSequence (fun n ↦ X n)))
    (c : Z × Z × T → ℂ) {n : ℕ} (ξ : Z × X n → ℂ) :
    ∑ p, c p * localizationVectorState X T ξ p =
      star ξ ⬝ᵥ (localizationQuadMatrix X T c n *ᵥ ξ) := by
  simp only [localizationVectorState, localizationQuadMatrix, Matrix.mulVec, dotProduct,
    Matrix.of_apply, localizationCoeff_apply, Pi.star_apply, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset (X n))) (t := (Finset.univ : Finset Z))]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset T)) (t := (Finset.univ : Finset (X n)))]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset T)) (t := (Finset.univ : Finset (X n)))]
  refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun t _ ↦ ?_
  ring

/-- Real rescaling scales the quadratic form by the square. -/
theorem localization_quadForm_smul {W : Type} [Fintype W] (H : Matrix W W ℂ) (ξ : W → ℂ)
    (r : ℝ) :
    (star ((r : ℂ) • ξ) ⬝ᵥ (H *ᵥ ((r : ℂ) • ξ))).re = r ^ 2 * (star ξ ⬝ᵥ (H *ᵥ ξ)).re := by
  rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul, sq]

theorem localization_nonpos_of_forall_sq_mul_le {a b : ℝ} (h : ∀ r : ℝ, r ^ 2 * a ≤ b) :
    a ≤ 0 := by
  by_contra ha
  push Not at ha
  have h1 := h (Real.sqrt ((|b| + 1) / a))
  rw [Real.sq_sqrt (div_nonneg (by positivity) ha.le), div_mul_cancel₀ _ ha.ne'] at h1
  linarith [le_abs_self b]

theorem localization_sum_neg_re {Z : Type} [Fintype Z] {k : ℕ} (e : Z ≃ Fin k)
    (h : Z → Z → ℂ) :
    (∑ l : Fin k, ∑ i : Fin k, -(h (e.symm l) (e.symm i) + star (h (e.symm i) (e.symm l)))).re =
      -(2 * (∑ a, ∑ b, h a b).re) := by
  have h1 : ∑ l : Fin k, ∑ i : Fin k, h (e.symm l) (e.symm i) = ∑ a, ∑ b, h a b :=
    (Equiv.sum_comp e.symm (fun a ↦ ∑ i : Fin k, h a (e.symm i))).trans
      (Finset.sum_congr rfl fun a _ ↦ Equiv.sum_comp e.symm (h a))
  have h2 : ∑ l : Fin k, ∑ i : Fin k, star (h (e.symm i) (e.symm l)) =
      star (∑ a, ∑ b, h a b) := by
    rw [Finset.sum_comm, ← h1, star_sum]
    exact Finset.sum_congr rfl fun l _ ↦ (star_sum _ _).symm
  simp only [Finset.sum_neg_distrib, Finset.sum_add_distrib]
  rw [h1, h2, Complex.neg_re, Complex.add_re, Complex.star_def, Complex.conj_re, two_mul]

/-- Summing the `(g i, g j)` entries of the `(i, j)` entries of a Gram matrix gives a number
with nonnegative real part. -/
theorem localization_re_sum_starMul_nonneg {m : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]
    [Nonempty Z] (g : Fin m → Z) (P : CStarMatrix (Fin m) (Fin m) (Matrix Z Z ℂ)) :
    0 ≤ (∑ i, ∑ j, ((star P * P) i j) (g i) (g j)).re := by
  have hentry : ∀ i j, ((star P * P) i j) (g i) (g j) =
      ∑ r, ∑ k, star (P r i k (g i)) * P r j k (g j) := by
    intro i j
    rw [cstarMatrix_mul_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [cstarMatrix_star_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Matrix.star_apply]
  have hsum : ∑ i, ∑ j, ((star P * P) i j) (g i) (g j) =
      ∑ r, ∑ k, star (∑ i, P r i k (g i)) * ∑ j, P r j k (g j) := by
    calc ∑ i, ∑ j, ((star P * P) i j) (g i) (g j)
        = ∑ i, ∑ j, ∑ r, ∑ k, star (P r i k (g i)) * P r j k (g j) :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hentry i j
      _ = ∑ i, ∑ r, ∑ j, ∑ k, star (P r i k (g i)) * P r j k (g j) :=
          Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
      _ = ∑ r, ∑ i, ∑ j, ∑ k, star (P r i k (g i)) * P r j k (g j) := Finset.sum_comm
      _ = ∑ r, ∑ i, ∑ k, ∑ j, star (P r i k (g i)) * P r j k (g j) :=
          Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
      _ = ∑ r, ∑ k, ∑ i, ∑ j, star (P r i k (g i)) * P r j k (g j) :=
          Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
      _ = ∑ r, ∑ k, star (∑ i, P r i k (g i)) * ∑ j, P r j k (g j) :=
          Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun k _ ↦ by
            rw [star_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ ↦ (Finset.mul_sum _ _ _).symm
  rw [hsum, Complex.re_sum]
  refine Finset.sum_nonneg fun r _ ↦ ?_
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun k _ ↦ ?_
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- The blocks of a Gram factor reproduce `-(H + Hᴴ)` blockwise. -/
theorem localization_gram_block {Z W : Type} [Fintype Z] [Fintype W]
    (H G : Matrix (Z × W) (Z × W) ℂ) (hG : -(H + H.conjTranspose) = star G * G) (l i : Z)
    (a b : W) :
    ∑ r, (star (localizationBlockEntry G r l) * localizationBlockEntry G r i) a b =
      -(H (l, a) (i, b) + star (H (i, b) (l, a))) := by
  have hA := congrFun (congrFun hG (l, a)) (i, b)
  rw [Matrix.neg_apply, Matrix.add_apply, Matrix.conjTranspose_apply, Matrix.mul_apply,
    Fintype.sum_prod_type] at hA
  rw [hA]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Matrix.star_apply, Matrix.star_apply, localizationBlockEntry_apply,
    localizationBlockEntry_apply]

/-- **Vector states support a CP map that kills the tail ideal.** Every complex functional is
nearly maximized, at the target point `Φ̂`, by a vector state at a coordinate `n ≥ N`. -/
theorem localization_support (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)] {Z : Type}
    [Fintype Z] [DecidableEq Z] [Nonempty Z]
    (T : Finset (BoundedMatrixSequence (fun n ↦ X n)))
    (Φ : BoundedMatrixSequence (fun n ↦ X n) →ₗ[ℂ] Matrix Z Z ℂ)
    (hΦ : IsCompletelyPositive Φ) (N : ℕ)
    (htail : ∀ x : BoundedMatrixSequence (fun n ↦ X n), (∀ n, N ≤ n → x n = 0) → Φ x = 0)
    (f : (Z × Z × T → ℂ) →L[ℂ] ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ z ∈ localizationVectorStateSet X Z T N,
      (f (localizationTarget X T Φ)).re < (f z).re + δ := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc⟩ := localization_exists_coeff f
  have hFexp : f (localizationTarget X T Φ) =
      ∑ i, ∑ j, Φ (localizationCoeff X T c i j) i j := by
    rw [hc, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [localizationCoeff, map_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [map_smul, Matrix.smul_apply]
    exact (smul_eq_mul _ _).symm
  have hform : ∀ n, N ≤ n → ∀ ξ : Z × X n → ℂ,
      (star ξ ⬝ᵥ (localizationQuadMatrix X T c n *ᵥ ξ)).re ≤ 0 := by
    intro n hn ξ
    refine localization_nonpos_of_forall_sq_mul_le
      (b := (f (localizationTarget X T Φ)).re - δ) fun r ↦ ?_
    have h1 := hcon (localizationVectorState X T ((r : ℂ) • ξ)) ⟨n, hn, (r : ℂ) • ξ, rfl⟩
    rw [hc (localizationVectorState X T ((r : ℂ) • ξ)), localization_sum_coeff_vectorState,
      localization_quadForm_smul] at h1
    linarith
  have hδF : δ ≤ (f (localizationTarget X T Φ)).re := by
    have h1 := hcon (localizationVectorState X T (0 : Z × X N → ℂ)) ⟨N, le_rfl, 0, rfl⟩
    rw [hc (localizationVectorState X T (0 : Z × X N → ℂ)),
      localization_sum_coeff_vectorState] at h1
    simp only [Matrix.mulVec_zero, dotProduct_zero, Complex.zero_re, zero_add] at h1
    exact h1
  have hG : ∀ n, ∃ G : Matrix (Z × X n) (Z × X n) ℂ,
      (N ≤ n → -(localizationQuadMatrix X T c n +
        (localizationQuadMatrix X T c n).conjTranspose) = star G * G) ∧
      (¬ N ≤ n → G = 0) := by
    intro n
    by_cases hn : N ≤ n
    · obtain ⟨G, hG⟩ := localization_exists_gram_of_quadForm_re_nonpos _ (hform n hn)
      exact ⟨G, fun _ ↦ hG, fun h ↦ absurd hn h⟩
    · exact ⟨0, fun h ↦ absurd h hn, fun _ ↦ rfl⟩
  choose G hGeq hGzero using hG
  have hGbound : ∀ n (l i : Z), ‖localizationBlockEntry (G n) l i‖ ≤
      1 + 2 * ∑ a, ∑ b, ‖localizationCoeff X T c a b‖ := by
    intro n l i
    refine (norm_localizationBlockEntry_le (G n) l i).trans ?_
    by_cases hn : N ≤ n
    · have hC0 : 0 ≤ ∑ a, ∑ b, ‖localizationCoeff X T c a b‖ := by positivity
      have hsq : ‖G n‖ * ‖G n‖ ≤ 2 * ∑ a, ∑ b, ‖localizationCoeff X T c a b‖ := by
        rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ← Matrix.star_eq_conjTranspose,
          ← hGeq n hn, norm_neg]
        refine (norm_add_le _ _).trans ?_
        rw [Matrix.l2_opNorm_conjTranspose, ← two_mul]
        refine mul_le_mul_of_nonneg_left
          ((norm_le_sum_localizationBlockEntry _).trans ?_) zero_le_two
        refine Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ ?_
        rw [localizationBlockEntry_quadMatrix]
        exact boundedMatrixSequence_coord_norm_le _ _ n
      nlinarith [sq_nonneg (‖G n‖ - 1), hC0, hsq]
    · rw [hGzero n hn, norm_zero]
      positivity
  obtain ⟨e⟩ : Nonempty (Z ≃ Fin (Fintype.card Z)) := ⟨Fintype.equivFin Z⟩
  have hmem : ∀ l i : Fin (Fintype.card Z),
      Memℓp (fun n ↦ localizationBlockEntry (G n) (e.symm l) (e.symm i)) ∞ := fun l i ↦
    memℓp_infty ⟨1 + 2 * ∑ a, ∑ b, ‖localizationCoeff X T c a b‖, by
      rintro _ ⟨n, rfl⟩
      exact hGbound n (e.symm l) (e.symm i)⟩
  obtain ⟨Nm, hNm⟩ : ∃ Nm : CStarMatrix (Fin (Fintype.card Z)) (Fin (Fintype.card Z))
      (BoundedMatrixSequence (fun n ↦ X n)),
      ∀ l i n, Nm l i n = localizationBlockEntry (G n) (e.symm l) (e.symm i) :=
    ⟨CStarMatrix.ofMatrix (Matrix.of fun l i ↦
      (⟨fun n ↦ localizationBlockEntry (G n) (e.symm l) (e.symm i), hmem l i⟩ :
        BoundedMatrixSequence (fun n ↦ X n))), fun _ _ _ ↦ rfl⟩
  obtain ⟨P, hP⟩ := hΦ _ (star Nm * Nm) ⟨Nm, rfl⟩
  have hcoord : ∀ l i n, N ≤ n → ((star Nm * Nm) l i) n =
      (-(localizationCoeff X T c (e.symm l) (e.symm i) +
        star (localizationCoeff X T c (e.symm i) (e.symm l)))) n := by
    intro l i n hn
    have hsum : ((star Nm * Nm) l i) n = ∑ r, star (localizationBlockEntry (G n) (e.symm r)
        (e.symm l)) * localizationBlockEntry (G n) (e.symm r) (e.symm i) := by
      rw [cstarMatrix_mul_apply, lp.coeFn_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      rw [cstarMatrix_star_apply, lp.infty_coeFn_mul, Pi.mul_apply, lp.star_apply, hNm, hNm]
    rw [hsum, Equiv.sum_comp e.symm (fun r ↦ star (localizationBlockEntry (G n) r (e.symm l)) *
      localizationBlockEntry (G n) r (e.symm i))]
    refine Matrix.ext fun a b ↦ ?_
    rw [Matrix.sum_apply, localization_gram_block _ (G n) (hGeq n hn)]
    rfl
  have hΦentry : ∀ l i, Φ ((star Nm * Nm) l i) =
      -(Φ (localizationCoeff X T c (e.symm l) (e.symm i)) +
        star (Φ (localizationCoeff X T c (e.symm i) (e.symm l)))) := by
    intro l i
    have h0 := htail ((star Nm * Nm) l i -
      -(localizationCoeff X T c (e.symm l) (e.symm i) +
        star (localizationCoeff X T c (e.symm i) (e.symm l)))) fun n hn ↦ by
      rw [lp.coeFn_sub, Pi.sub_apply, sub_eq_zero]
      exact hcoord l i n hn
    rw [map_sub, sub_eq_zero, map_neg, map_add, OrderZero.map_star_of_cp hΦ] at h0
    exact h0
  have hsumeq : ∑ l, ∑ i, ((star P * P) l i) (e.symm l) (e.symm i) =
      ∑ l, ∑ i, -(Φ (localizationCoeff X T c (e.symm l) (e.symm i)) (e.symm l) (e.symm i) +
        star (Φ (localizationCoeff X T c (e.symm i) (e.symm l)) (e.symm i) (e.symm l))) := by
    rw [← hP]
    refine Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    rw [CStarMatrix.map_apply, hΦentry l i]
    rfl
  have hkey := (localization_re_sum_starMul_nonneg e.symm P).trans_eq
    ((congrArg Complex.re hsumeq).trans
      (localization_sum_neg_re e fun a b ↦ Φ (localizationCoeff X T c a b) a b))
  rw [hFexp] at hδF
  linarith

end

end RelatedBK
end NonMF
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMF.RelatedBK

#audit_axioms localizationVectorState
#audit_axioms localizationVectorStateSet
#audit_axioms localizationTarget
#audit_axioms localizationCoeff
#audit_axioms localizationCoeff_apply
#audit_axioms localizationQuadMatrix
#audit_axioms localizationBlockEntry_quadMatrix
#audit_axioms localization_exists_coeff
#audit_axioms localization_sum_coeff_vectorState
#audit_axioms localization_quadForm_smul
#audit_axioms localization_nonpos_of_forall_sq_mul_le
#audit_axioms localization_sum_neg_re
#audit_axioms localization_re_sum_starMul_nonneg
#audit_axioms localization_gram_block
#audit_axioms localization_support
