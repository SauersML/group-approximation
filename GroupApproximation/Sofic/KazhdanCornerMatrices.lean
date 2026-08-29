import GroupApproximation.Sofic.OpAlmostRepresentation
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Finite matrix averages for the Kazhdan corner

This file begins the finite-stage transfer of the constructive Kazhdan
projection.  Weak-MF microstates are not assumed to preserve the identity or
inverses exactly, but unitarity and asymptotic multiplicativity force both
properties in operator norm.  Consequently the orbit average over a symmetric
finite set is asymptotically self-adjoint.  Its later spectral projection is
the finite-dimensional lift of the Kazhdan corner.
-/

namespace GroupApproximation
namespace KazhdanCornerMatrices

open Matrix
open scoped Matrix.Norms.L2Operator

variable {G : Type*} [Group G]

/-- Operator-norm convergence to zero for a dependent sequence of matrices. -/
def OpNormVanishing (A : OpAlmostRepresentation G)
    (x : ∀ n, Matrix (A.model n) (A.model n) ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, ‖x n‖ ≤ ε

theorem OpNormVanishing.congr {A : OpAlmostRepresentation G}
    {x y : ∀ n, Matrix (A.model n) (A.model n) ℂ}
    (hx : OpNormVanishing A x) (hxy : ∀ n, x n = y n) :
    OpNormVanishing A y := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  exact ⟨N, fun n hn ↦ by rw [← hxy n]; exact hN n hn⟩

theorem opNormVanishing_zero (A : OpAlmostRepresentation G) :
    OpNormVanishing A (fun n ↦ (0 : Matrix (A.model n) (A.model n) ℂ)) := by
  intro ε hε
  exact ⟨0, fun n _ ↦ by simp [hε.le]⟩

theorem OpNormVanishing.neg {A : OpAlmostRepresentation G}
    {x : ∀ n, Matrix (A.model n) (A.model n) ℂ}
    (hx : OpNormVanishing A x) : OpNormVanishing A (fun n ↦ -x n) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  exact ⟨N, fun n hn ↦ by rw [norm_neg]; exact hN n hn⟩

theorem OpNormVanishing.add {A : OpAlmostRepresentation G}
    {x y : ∀ n, Matrix (A.model n) (A.model n) ℂ}
    (hx : OpNormVanishing A x) (hy : OpNormVanishing A y) :
    OpNormVanishing A (fun n ↦ x n + y n) := by
  intro ε hε
  obtain ⟨Nx, hNx⟩ := hx (ε / 2) (half_pos hε)
  obtain ⟨Ny, hNy⟩ := hy (ε / 2) (half_pos hε)
  refine ⟨max Nx Ny, fun n hn ↦ ?_⟩
  calc
    ‖x n + y n‖ ≤ ‖x n‖ + ‖y n‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add
      (hNx n ((le_max_left _ _).trans hn))
      (hNy n ((le_max_right _ _).trans hn))
    _ = ε := by ring

theorem OpNormVanishing.sub {A : OpAlmostRepresentation G}
    {x y : ∀ n, Matrix (A.model n) (A.model n) ℂ}
    (hx : OpNormVanishing A x) (hy : OpNormVanishing A y) :
    OpNormVanishing A (fun n ↦ x n - y n) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

theorem OpNormVanishing.smul {A : OpAlmostRepresentation G}
    {x : ∀ n, Matrix (A.model n) (A.model n) ℂ}
    (hx : OpNormVanishing A x) (c : ℂ) :
    OpNormVanishing A (fun n ↦ c • x n) := by
  intro ε hε
  have hden : 0 < ‖c‖ + 1 := by positivity
  obtain ⟨N, hN⟩ := hx (ε / (‖c‖ + 1)) (div_pos hε hden)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [norm_smul]
  calc
    ‖c‖ * ‖x n‖ ≤ ‖c‖ * (ε / (‖c‖ + 1)) :=
      mul_le_mul_of_nonneg_left (hN n hn) (norm_nonneg c)
    _ ≤ ε := by
      rw [show ‖c‖ * (ε / (‖c‖ + 1)) =
        (‖c‖ * ε) / (‖c‖ + 1) by ring, div_le_iff₀ hden]
      nlinarith only [norm_nonneg c, hε.le]

theorem OpNormVanishing.mul_left_of_norm_le_one
    {A : OpAlmostRepresentation G}
    {x : ∀ n, Matrix (A.model n) (A.model n) ℂ}
    (hx : OpNormVanishing A x)
    (b : ∀ n, Matrix (A.model n) (A.model n) ℂ)
    (hb : ∀ n, ‖b n‖ ≤ 1) :
    OpNormVanishing A (fun n ↦ b n * x n) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  calc
    ‖b n * x n‖ ≤ ‖b n‖ * ‖x n‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * ε := mul_le_mul (hb n) (hN n hn) (norm_nonneg _) zero_le_one
    _ = ε := one_mul _

theorem OpNormVanishing.mul_right_of_norm_le_one
    {A : OpAlmostRepresentation G}
    {x : ∀ n, Matrix (A.model n) (A.model n) ℂ}
    (hx : OpNormVanishing A x)
    (b : ∀ n, Matrix (A.model n) (A.model n) ℂ)
    (hb : ∀ n, ‖b n‖ ≤ 1) :
    OpNormVanishing A (fun n ↦ x n * b n) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  calc
    ‖x n * b n‖ ≤ ‖x n‖ * ‖b n‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ε * 1 := mul_le_mul (hN n hn) (hb n) (norm_nonneg _) hε.le
    _ = ε := mul_one _

theorem OpNormVanishing.finset_sum {A : OpAlmostRepresentation G}
    {I : Type*} (s : Finset I)
    (x : I → ∀ n, Matrix (A.model n) (A.model n) ℂ)
    (hx : ∀ i ∈ s, OpNormVanishing A (x i)) :
    OpNormVanishing A (fun n ↦ ∑ i ∈ s, x i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using opNormVanishing_zero A
  | @insert i s hi ih =>
      have hiV := hx i (Finset.mem_insert_self i s)
      have hsV := ih fun j hj ↦ hx j (Finset.mem_insert_of_mem hj)
      simpa [Finset.sum_insert, hi] using hiV.add hsV

/-- The defining multiplicative defects are operator-norm vanishing. -/
theorem multiplicativeDefect_vanishing (A : OpAlmostRepresentation G)
    (g h : G) :
    OpNormVanishing A (fun n ↦
      (A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) * A.map n h) :=
  A.asymptoticallyMultiplicative g h

/-- Unitary weak-MF microstates send the identity to the identity
asymptotically in operator norm. -/
theorem map_one_vanishing (A : OpAlmostRepresentation G) :
    OpNormVanishing A (fun n ↦
      (A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1) := by
  intro ε hε
  obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative 1 1 ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  let U : Matrix (A.model n) (A.model n) ℂ := A.map n 1
  have hfactor : U - U * U = (1 - U) * U := by
    rw [Matrix.sub_mul, one_mul]
  have hnorm : ‖U - 1‖ = ‖U - U * U‖ := by
    rw [hfactor, CStarRing.norm_mul_mem_unitary _ (A.map n 1).2]
    rw [show U - 1 = -(1 - U) by abel, norm_neg]
  rw [hnorm]
  simpa [U] using hN n hn

/-- Inversion of the group variable becomes conjugate transpose of the
microstate, asymptotically in operator norm. -/
theorem map_inv_vanishing (A : OpAlmostRepresentation G) (g : G) :
    OpNormVanishing A (fun n ↦
      (A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) := by
  intro ε hε
  obtain ⟨Nm, hNm⟩ := A.asymptoticallyMultiplicative g⁻¹ g (ε / 2) (half_pos hε)
  obtain ⟨N1, hN1⟩ := map_one_vanishing A (ε / 2) (half_pos hε)
  refine ⟨max Nm N1, fun n hn ↦ ?_⟩
  let U : Matrix (A.model n) (A.model n) ℂ := A.map n g
  let V : Matrix (A.model n) (A.model n) ℂ := A.map n g⁻¹
  let E : Matrix (A.model n) (A.model n) ℂ := A.map n 1
  have hUHU : Uᴴ * U = 1 := by
    have h := (A.map n g).2
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
    exact h
  have hfactor : (V - Uᴴ) * U = V * U - 1 := by
    rw [Matrix.sub_mul, hUHU]
  have hnorm : ‖V - Uᴴ‖ = ‖V * U - 1‖ := by
    rw [← CStarRing.norm_mul_mem_unitary (V - Uᴴ) (A.map n g).2,
      hfactor]
  rw [hnorm]
  calc
    ‖V * U - 1‖ ≤ ‖V * U - E‖ + ‖E - 1‖ := by
      rw [show V * U - 1 = (V * U - E) + (E - 1) by abel]
      exact norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add
      (by
        rw [show V * U - E = -(E - V * U) by abel, norm_neg]
        simpa [V, U, E] using hNm n ((le_max_left _ _).trans hn))
      (by simpa [E] using hN1 n ((le_max_right _ _).trans hn))
    _ = ε := by ring

/-- Relative products of weak-MF microstates agree asymptotically with the
exact Hilbert-space relative operator. -/
theorem map_inv_mul_vanishing (A : OpAlmostRepresentation G) (g h : G) :
    OpNormVanishing A (fun n ↦
      (A.map n (g⁻¹ * h) : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ * A.map n h) := by
  intro ε hε
  obtain ⟨Nm, hNm⟩ :=
    A.asymptoticallyMultiplicative g⁻¹ h (ε / 2) (half_pos hε)
  obtain ⟨Ni, hNi⟩ := map_inv_vanishing A g (ε / 2) (half_pos hε)
  refine ⟨max Nm Ni, fun n hn ↦ ?_⟩
  let V : Matrix (A.model n) (A.model n) ℂ := A.map n g⁻¹
  let Ustar : Matrix (A.model n) (A.model n) ℂ :=
    (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ
  let W : Matrix (A.model n) (A.model n) ℂ := A.map n h
  have hsplit :
      (A.map n (g⁻¹ * h) : Matrix (A.model n) (A.model n) ℂ) -
          Ustar * W =
        ((A.map n (g⁻¹ * h) : Matrix (A.model n) (A.model n) ℂ) -
          V * W) + (V - Ustar) * W := by
    noncomm_ring
  change ‖(A.map n (g⁻¹ * h) : Matrix (A.model n) (A.model n) ℂ) -
    Ustar * W‖ ≤ ε
  rw [hsplit]
  calc
    ‖((A.map n (g⁻¹ * h) : Matrix (A.model n) (A.model n) ℂ) -
          V * W) + (V - Ustar) * W‖ ≤
        ‖(A.map n (g⁻¹ * h) : Matrix (A.model n) (A.model n) ℂ) -
          V * W‖ + ‖(V - Ustar) * W‖ := norm_add_le _ _
    _ = ‖(A.map n (g⁻¹ * h) : Matrix (A.model n) (A.model n) ℂ) -
          V * W‖ + ‖V - Ustar‖ := by
      rw [CStarRing.norm_mul_mem_unitary _ (A.map n h).2]
    _ ≤ ε / 2 + ε / 2 := add_le_add
      (by simpa [V, W] using hNm n ((le_max_left _ _).trans hn))
      (by simpa [V, Ustar] using hNi n ((le_max_right _ _).trans hn))
    _ = ε := by ring

/-- The finite-stage orbit average evaluated in weak-MF microstates. -/
noncomputable def matrixAverage (A : OpAlmostRepresentation G) (S : Finset G)
    (n : ℕ) : Matrix (A.model n) (A.model n) ℂ :=
  ((S.card : ℂ)⁻¹) • ∑ g ∈ S,
    (A.map n g : Matrix (A.model n) (A.model n) ℂ)

/-- Every finite-stage unitary orbit average has operator norm at most one. -/
theorem norm_matrixAverage_le_one (A : OpAlmostRepresentation G) (S : Finset G)
    (n : ℕ) : ‖matrixAverage A S n‖ ≤ 1 := by
  classical
  by_cases hS : S = ∅
  · subst S
    simp [matrixAverage]
  have hcardNat : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  letI : Nonempty (A.model n) := Fintype.card_pos_iff.mp (A.modelNonempty n)
  have hunitary (g : G) :
      ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ)‖ = 1 :=
    CStarRing.norm_of_mem_unitary (A.map n g).2
  rw [matrixAverage, norm_smul]
  have hcoef : ‖((S.card : ℂ)⁻¹)‖ = (S.card : ℝ)⁻¹ := by
    rw [norm_inv]
    simp
  rw [hcoef]
  calc
    (S.card : ℝ)⁻¹ * ‖∑ g ∈ S,
        (A.map n g : Matrix (A.model n) (A.model n) ℂ)‖ ≤
        (S.card : ℝ)⁻¹ * ∑ g ∈ S, ‖(A.map n g :
          Matrix (A.model n) (A.model n) ℂ)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hcard.le)
    _ = (S.card : ℝ)⁻¹ * S.card := by simp_rw [hunitary]; simp
    _ = 1 := inv_mul_cancel₀ hcard.ne'

/-- A symmetric averaging set makes the weak-MF matrix average
asymptotically self-adjoint. -/
theorem matrixAverage_selfAdjoint_vanishing (A : OpAlmostRepresentation G)
    (S : Finset G) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) :
    OpNormVanishing A (fun n ↦ matrixAverage A S n -
      (matrixAverage A S n)ᴴ) := by
  classical
  have hinvsum (n : ℕ) :
      (∑ g ∈ S, (A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ)) =
        ∑ g ∈ S, (A.map n g : Matrix (A.model n) (A.model n) ℂ) :=
    Finset.sum_bij'
      (fun g _ ↦ g⁻¹) (fun g _ ↦ g⁻¹)
      (fun g hg ↦ hsymm g hg) (fun g hg ↦ hsymm g hg)
      (fun g _ ↦ by simp) (fun g _ ↦ by simp) (fun g _ ↦ rfl)
  have hsum (n : ℕ) :
      (∑ g ∈ S, ((A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ)) =
        (∑ g ∈ S, (A.map n g : Matrix (A.model n) (A.model n) ℂ)) -
          (∑ g ∈ S, (A.map n g : Matrix (A.model n) (A.model n) ℂ))ᴴ := by
    rw [Finset.sum_sub_distrib, hinvsum]
    simp only [Matrix.conjTranspose_sum]
  have hv : OpNormVanishing A (fun n ↦
      ∑ g ∈ S, ((A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ)) :=
    OpNormVanishing.finset_sum S
      (fun g n ↦ (A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ)
      (fun g _ ↦ map_inv_vanishing A g)
  have hrewrite (n : ℕ) : matrixAverage A S n -
      (matrixAverage A S n)ᴴ =
        ((S.card : ℂ)⁻¹) •
          (∑ g ∈ S, ((A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ) -
            (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ)) := by
    rw [matrixAverage, Matrix.conjTranspose_smul]
    simp only [Matrix.conjTranspose_sum]
    have hcstar : star (((S.card : ℂ)⁻¹)) = (S.card : ℂ)⁻¹ := by simp
    have hsum' :
        (∑ g ∈ S, ((A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ)) =
          (∑ g ∈ S, (A.map n g : Matrix (A.model n) (A.model n) ℂ)) -
            ∑ g ∈ S, (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ := by
      simpa only [Matrix.conjTranspose_sum] using hsum n
    rw [hcstar, ← smul_sub, ← hsum']
  simpa only [hrewrite] using hv.smul ((S.card : ℂ)⁻¹)

/-- Exact Hermitian symmetrization of the finite-stage orbit average. -/
noncomputable def hermitianAverage (A : OpAlmostRepresentation G) (S : Finset G)
    (n : ℕ) : Matrix (A.model n) (A.model n) ℂ :=
  (2 : ℂ)⁻¹ • (matrixAverage A S n + (matrixAverage A S n)ᴴ)

theorem hermitianAverage_conjTranspose (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) :
    (hermitianAverage A S n)ᴴ = hermitianAverage A S n := by
  rw [hermitianAverage, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_conjTranspose]
  have hc : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by norm_num
  rw [hc, add_comm]

/-- Hermitian symmetrization does not increase the unit-ball bound. -/
theorem norm_hermitianAverage_le_one (A : OpAlmostRepresentation G)
    (S : Finset G) (n : ℕ) : ‖hermitianAverage A S n‖ ≤ 1 := by
  rw [hermitianAverage, norm_smul]
  have hc : ‖((2 : ℂ)⁻¹)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hc]
  calc
    (1 / 2 : ℝ) * ‖matrixAverage A S n + (matrixAverage A S n)ᴴ‖ ≤
        (1 / 2 : ℝ) *
          (‖matrixAverage A S n‖ + ‖(matrixAverage A S n)ᴴ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = (1 / 2 : ℝ) * (2 * ‖matrixAverage A S n‖) := by
      rw [← Matrix.star_eq_conjTranspose, norm_star]
      ring
    _ = ‖matrixAverage A S n‖ := by ring
    _ ≤ 1 := norm_matrixAverage_le_one A S n

/-- The exact Hermitian average is asymptotically equal to the original
weak-MF average. -/
theorem matrixAverage_sub_hermitian_vanishing (A : OpAlmostRepresentation G)
    (S : Finset G) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) :
    OpNormVanishing A (fun n ↦ matrixAverage A S n -
      hermitianAverage A S n) := by
  have hv := matrixAverage_selfAdjoint_vanishing A S hsymm
  have hrewrite (n : ℕ) : matrixAverage A S n - hermitianAverage A S n =
      (2 : ℂ)⁻¹ • (matrixAverage A S n - (matrixAverage A S n)ᴴ) := by
    ext i j
    simp [hermitianAverage]
    ring
  simpa only [hrewrite] using hv.smul ((2 : ℂ)⁻¹)

/-! ## Finite spectral projections -/

/-- A matrix is an orthogonal projection when it is Hermitian and
idempotent. -/
def IsOrthogonalProjectionMatrix {Y : Type*} [Fintype Y]
    (P : Matrix Y Y ℂ) : Prop := Pᴴ = P ∧ P * P = P

/-- Spectral projection of a Hermitian matrix onto eigenvalues strictly above
`t`, written in its orthonormal eigenbasis. -/
noncomputable def spectralAbove {Y : Type*} [Fintype Y] [DecidableEq Y]
    (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (t : ℝ) : Matrix Y Y ℂ :=
  let U : Matrix Y Y ℂ := hH.eigenvectorUnitary
  U * Matrix.diagonal (fun i ↦ if t < hH.eigenvalues i then 1 else 0) * Uᴴ

/-- The diagonal cutoff used in `spectralAbove` is an orthogonal projection.
-/
theorem spectralDiagonal_isOrthogonalProjection {Y : Type*} [Fintype Y]
    [DecidableEq Y] (f : Y → Prop) [DecidablePred f] :
    IsOrthogonalProjectionMatrix
      (Matrix.diagonal fun i : Y ↦ if f i then (1 : ℂ) else 0) := by
  constructor
  · ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.conjTranspose_apply]
    · simp [Matrix.conjTranspose_apply, hij, Ne.symm hij]
  · rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]

/-- A unitary conjugate of an orthogonal projection is again an orthogonal
projection. -/
theorem unitary_conjugate_isOrthogonalProjection {Y : Type*} [Fintype Y]
    [DecidableEq Y] {U P : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ)
    (hP : IsOrthogonalProjectionMatrix P) :
    IsOrthogonalProjectionMatrix (U * P * Uᴴ) := by
  have hUU : Uᴴ * U = 1 := by
    have h := hU
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h
    exact h
  constructor
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hP.1]
    simp only [mul_assoc]
  · calc
      (U * P * Uᴴ) * (U * P * Uᴴ) =
          U * P * (Uᴴ * U) * P * Uᴴ := by noncomm_ring
      _ = U * (P * P) * Uᴴ := by rw [hUU]; noncomm_ring
      _ = U * P * Uᴴ := by rw [hP.2]

/-- Every Hermitian spectral cutoff is an orthogonal projection. -/
theorem spectralAbove_isOrthogonalProjection {Y : Type*} [Fintype Y]
    [DecidableEq Y] (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (t : ℝ) :
    IsOrthogonalProjectionMatrix (spectralAbove H hH t) := by
  unfold spectralAbove
  exact unitary_conjugate_isOrthogonalProjection
    hH.eigenvectorUnitary.2 (spectralDiagonal_isOrthogonalProjection _)

/-- Complementary spectral cutoff, the finite-stage moving corner. -/
noncomputable def spectralBelow {Y : Type*} [Fintype Y] [DecidableEq Y]
    (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (t : ℝ) : Matrix Y Y ℂ :=
  1 - spectralAbove H hH t

theorem one_sub_isOrthogonalProjection {Y : Type*} [Fintype Y]
    [DecidableEq Y] {P : Matrix Y Y ℂ}
    (hP : IsOrthogonalProjectionMatrix P) :
    IsOrthogonalProjectionMatrix (1 - P) := by
  constructor
  · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.1]
  · calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP.2]; abel

end KazhdanCornerMatrices
end GroupApproximation
