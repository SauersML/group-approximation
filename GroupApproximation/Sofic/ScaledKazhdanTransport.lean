import GroupApproximation.Sofic.KazhdanAsymptoticCommutant

/-!
# Kazhdan transport of asymptotic commutants at every scale

`Sofic.KazhdanAsymptoticCommutant` proves that a one-sided compressor of a
Kazhdan image preserves the *normalized* Hilbert--Schmidt asymptotic
commutant of an operator-norm almost representation, for uniformly
operator-norm-bounded sequences.  The normalization there is by the matrix
dimension, which makes the statement blind to phenomena carried on
`o(dₙ)`-dimensional subspaces ("rank blindness").

This file removes the normalization.  Fix an arbitrary nonnegative weight
sequence `w : ℕ → ℝ`.  A matrix sequence is *`w`-mass vanishing* when its
unnormalized Frobenius mass is eventually below `ε · w n` for every `ε`, and
*`w`-mass bounded* when its Frobenius mass is `O(w n)`.  The main theorems
prove that a one-sided compressor of a Kazhdan image acts in both directions
on the `w`-mass-bounded, `w`-scaled asymptotic commutant — for **every**
weight `w` at once.

Taking `w n = Fintype.card (model n)` recovers (and strictly strengthens:
mass boundedness is weaker than operator-norm boundedness) the normalized
theorem.  Taking `w n` to be a rank scale, e.g. the total rank displacement
of a family of finite-spectrum lamps, is the calibration under which the
compression-collapse argument for lamp coordinates operates; the transported
fixed-space identity proved here is the "matricial Mautner lemma with
arbitrary scalar rescaling" used by that argument.

The Kazhdan corner, its displacement bounds, and the equal-rank flip
(`Sofic.KazhdanCompressorCorner`) are purely operator-norm statements on the
adjoint model and are reused verbatim.  Only the capture step and the final
mass bookkeeping see the weight, and both are dimension-free.
-/

namespace GroupApproximation
namespace ScaledKazhdanTransport

open Matrix KazhdanCornerMatrices KazhdanCompressorCorner
open KazhdanAsymptoticCommutant
open scoped Matrix.Norms.L2Operator

universe u v

/-! The ambient group is quantified at an arbitrary universe, matching the
manuscript, which fixes no universe for the group `H` carrying the almost
representation.  See `Sofic.KazhdanAsymptoticCommutant` for why the Kazhdan
source `Γ` stays in `Type 0`. -/
variable {Γ : Type} {E : Type u} [Group Γ] [Group E]

/-! ## Unnormalized Frobenius mass -/

/-- The unnormalized squared Frobenius mass of a square matrix. -/
noncomputable def matMass {Y : Type*} [Fintype Y] (X : Matrix Y Y ℂ) : ℝ :=
  ∑ i : Y, ∑ j : Y, Complex.normSq (X i j)

theorem matMass_nonneg {Y : Type*} [Fintype Y] (X : Matrix Y Y ℂ) :
    0 ≤ matMass X :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
    Complex.normSq_nonneg _

theorem matMass_zero {Y : Type*} [Fintype Y] :
    matMass (0 : Matrix Y Y ℂ) = 0 := by
  simp [matMass]

theorem matMass_neg {Y : Type*} [Fintype Y] (X : Matrix Y Y ℂ) :
    matMass (-X) = matMass X := by
  unfold matMass
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Matrix.neg_apply, Complex.normSq_neg]

theorem matMass_smul {Y : Type*} [Fintype Y] (c : ℂ) (X : Matrix Y Y ℂ) :
    matMass (c • X) = Complex.normSq c * matMass X := by
  unfold matMass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  show Complex.normSq (c * X i j) = _
  rw [Complex.normSq_mul]

theorem matMass_add_le {Y : Type*} [Fintype Y] (X Z : Matrix Y Y ℂ) :
    matMass (X + Z) ≤ 2 * matMass X + 2 * matMass Z := by
  have hentry : ∀ i j : Y, Complex.normSq ((X + Z) i j)
      ≤ 2 * Complex.normSq (X i j) + 2 * Complex.normSq (Z i j) := by
    intro i j
    show Complex.normSq (X i j + Z i j) ≤ _
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
    nlinarith [sq_nonneg ((X i j).re - (Z i j).re),
      sq_nonneg ((X i j).im - (Z i j).im)]
  unfold matMass
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ ↦ hentry i j

theorem matMass_conjTranspose {Y : Type*} [Fintype Y] (X : Matrix Y Y ℂ) :
    matMass Xᴴ = matMass X := by
  unfold matMass
  calc
    (∑ i : Y, ∑ j : Y, Complex.normSq (Xᴴ i j)) =
        ∑ i : Y, ∑ j : Y, Complex.normSq (X j i) := by
      refine Finset.sum_congr rfl fun i _ ↦
        Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Matrix.conjTranspose_apply]
      exact Complex.normSq_conj _
    _ = ∑ j : Y, ∑ i : Y, Complex.normSq (X j i) := Finset.sum_comm

/-- Left multiplication is controlled by the operator norm, with no
dimension factor. -/
theorem matMass_mul_le_left {Y : Type*} [Fintype Y] [DecidableEq Y]
    (A X : Matrix Y Y ℂ) : matMass (A * X) ≤ ‖A‖ ^ 2 * matMass X := by
  have hcol : ∀ j i : Y, (A * X) i j = (A *ᵥ fun k ↦ X k j) i := by
    intro j i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  unfold matMass
  calc
    (∑ i : Y, ∑ j : Y, Complex.normSq ((A * X) i j)) =
        ∑ j : Y, ∑ i : Y, Complex.normSq ((A * X) i j) := Finset.sum_comm
    _ = ∑ j : Y, ∑ i : Y, Complex.normSq ((A *ᵥ fun k ↦ X k j) i) := by
      refine Finset.sum_congr rfl fun j _ ↦
        Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hcol j i]
    _ ≤ ∑ j : Y, ‖A‖ ^ 2 * ∑ i : Y, Complex.normSq (X i j) :=
      Finset.sum_le_sum fun j _ ↦ sum_normSq_mulVec_le_general A _
    _ = ‖A‖ ^ 2 * ∑ j : Y, ∑ i : Y, Complex.normSq (X i j) := by
      rw [Finset.mul_sum]
    _ = ‖A‖ ^ 2 * ∑ i : Y, ∑ j : Y, Complex.normSq (X i j) :=
      congrArg _ Finset.sum_comm

/-- Right multiplication is controlled by the operator norm, with no
dimension factor. -/
theorem matMass_mul_le_right {Y : Type*} [Fintype Y] [DecidableEq Y]
    (X A : Matrix Y Y ℂ) : matMass (X * A) ≤ ‖A‖ ^ 2 * matMass X := by
  calc
    matMass (X * A) = matMass ((X * A)ᴴ) := (matMass_conjTranspose _).symm
    _ = matMass (Aᴴ * Xᴴ) := by rw [Matrix.conjTranspose_mul]
    _ ≤ ‖Aᴴ‖ ^ 2 * matMass Xᴴ := matMass_mul_le_left _ _
    _ = ‖A‖ ^ 2 * matMass X := by
      rw [matMass_conjTranspose, ← Matrix.star_eq_conjTranspose, norm_star]

/-- An isometric column matrix preserves Frobenius mass on the left. -/
theorem matMass_mul_left_of_star_mul_self {Y : Type*} [Fintype Y]
    [DecidableEq Y] {U : Matrix Y Y ℂ} (hU : Uᴴ * U = 1)
    (X : Matrix Y Y ℂ) : matMass (U * X) = matMass X := by
  have hcol : ∀ j i : Y, (U * X) i j = (U *ᵥ fun k ↦ X k j) i := by
    intro j i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  unfold matMass
  calc
    (∑ i : Y, ∑ j : Y, Complex.normSq ((U * X) i j)) =
        ∑ j : Y, ∑ i : Y, Complex.normSq ((U * X) i j) := Finset.sum_comm
    _ = ∑ j : Y, ∑ i : Y, Complex.normSq ((U *ᵥ fun k ↦ X k j) i) := by
      refine Finset.sum_congr rfl fun j _ ↦
        Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hcol j i]
    _ = ∑ j : Y, ∑ i : Y, Complex.normSq (X i j) :=
      Finset.sum_congr rfl fun j _ ↦
        sum_normSq_mulVec_of_star_mul_self hU _
    _ = ∑ i : Y, ∑ j : Y, Complex.normSq (X i j) := Finset.sum_comm

/-- A unitary matrix preserves Frobenius mass on the right. -/
theorem matMass_mul_right_of_mul_star_self {Y : Type*} [Fintype Y]
    [DecidableEq Y] {U : Matrix Y Y ℂ} (hU : U * Uᴴ = 1)
    (X : Matrix Y Y ℂ) : matMass (X * U) = matMass X := by
  have hstar : (Uᴴ)ᴴ * Uᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact hU
  calc
    matMass (X * U) = matMass ((X * U)ᴴ) := (matMass_conjTranspose _).symm
    _ = matMass (Uᴴ * Xᴴ) := by rw [Matrix.conjTranspose_mul]
    _ = matMass Xᴴ := matMass_mul_left_of_star_mul_self hstar _
    _ = matMass X := matMass_conjTranspose _

/-- Unitary conjugation preserves Frobenius mass exactly. -/
theorem matMass_unitary_conj {Y : Type*} [Fintype Y] [DecidableEq Y]
    {U : Matrix Y Y ℂ} (hU : U ∈ Matrix.unitaryGroup Y ℂ)
    (X : Matrix Y Y ℂ) : matMass (U * X * Uᴴ) = matMass X := by
  have hUstar : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have hUstar' : U * Uᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have hright : Uᴴ * (Uᴴ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact hUstar
  calc
    matMass (U * X * Uᴴ) = matMass ((U * X) * Uᴴ) := by
      rw [Matrix.mul_assoc]
    _ = matMass (U * X) := matMass_mul_right_of_mul_star_self hright _
    _ = matMass X := matMass_mul_left_of_star_mul_self hUstar _

/-- The flattened Frobenius mass of a matrix coordinate. -/
theorem vecMass_gammaRowVec (B : OpAlmostRepresentation E) (n : ℕ)
    (X : Matrix (B.model n) (B.model n) ℂ) :
    MarkedCompressionVectorChain.vecMass (gammaRowVec B n X) = matMass X := by
  unfold MarkedCompressionVectorChain.vecMass matMass
  exact sum_normSq_gammaRowVec B n X

/-! ## Scaled mass vanishing -/

/-- Frobenius-mass convergence to zero at scale `w`: for every `ε`, the mass
is eventually at most `ε * w n`. -/
def ScaledMassVanishing (B : OpAlmostRepresentation E) (w : ℕ → ℝ)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, matMass (x n) ≤ ε * w n

/-- The zero sequence vanishes at every nonnegative weight. -/
theorem scaledMassVanishing_zero (B : OpAlmostRepresentation E)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    ScaledMassVanishing B w
      (fun n ↦ (0 : Matrix (B.model n) (B.model n) ℂ)) := by
  intro ε hε
  refine ⟨0, fun n _ ↦ ?_⟩
  rw [matMass_zero]
  exact mul_nonneg hε.le (hw n)

theorem ScaledMassVanishing.congr {B : OpAlmostRepresentation E}
    {w : ℕ → ℝ} {x y : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : ScaledMassVanishing B w x) (hxy : ∀ n, x n = y n) :
    ScaledMassVanishing B w y := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  exact ⟨N, fun n hn ↦ by rw [← hxy n]; exact hN n hn⟩

theorem ScaledMassVanishing.neg {B : OpAlmostRepresentation E}
    {w : ℕ → ℝ} {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : ScaledMassVanishing B w x) :
    ScaledMassVanishing B w (fun n ↦ -x n) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [matMass_neg]
  exact hN n hn

/-- Reversing a difference preserves scaled mass nullity. -/
theorem ScaledMassVanishing.sub_symm {B : OpAlmostRepresentation E}
    {w : ℕ → ℝ} {x y : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hxy : ScaledMassVanishing B w (fun n ↦ x n - y n)) :
    ScaledMassVanishing B w (fun n ↦ y n - x n) :=
  hxy.neg.congr fun n ↦ by abel

theorem ScaledMassVanishing.add {B : OpAlmostRepresentation E}
    {w : ℕ → ℝ} {x y : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : ScaledMassVanishing B w x) (hy : ScaledMassVanishing B w y) :
    ScaledMassVanishing B w (fun n ↦ x n + y n) := by
  intro ε hε
  obtain ⟨Nx, hNx⟩ := hx (ε / 4) (by linarith)
  obtain ⟨Ny, hNy⟩ := hy (ε / 4) (by linarith)
  refine ⟨max Nx Ny, fun n hn ↦ ?_⟩
  have hx' := hNx n ((le_max_left _ _).trans hn)
  have hy' := hNy n ((le_max_right _ _).trans hn)
  calc
    matMass (x n + y n) ≤ 2 * matMass (x n) + 2 * matMass (y n) :=
      matMass_add_le _ _
    _ ≤ 2 * (ε / 4 * w n) + 2 * (ε / 4 * w n) := by gcongr
    _ = ε * w n := by ring

theorem ScaledMassVanishing.smul {B : OpAlmostRepresentation E}
    {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : ScaledMassVanishing B w x) (c : ℂ) :
    ScaledMassVanishing B w (fun n ↦ c • x n) := by
  intro ε hε
  have hden : 0 < Complex.normSq c + 1 := by
    nlinarith [Complex.normSq_nonneg c]
  obtain ⟨N, hN⟩ := hx (ε / (Complex.normSq c + 1)) (div_pos hε hden)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [matMass_smul]
  calc
    Complex.normSq c * matMass (x n) ≤
        Complex.normSq c * (ε / (Complex.normSq c + 1) * w n) :=
      mul_le_mul_of_nonneg_left (hN n hn) (Complex.normSq_nonneg c)
    _ = (Complex.normSq c / (Complex.normSq c + 1)) * (ε * w n) := by ring
    _ ≤ 1 * (ε * w n) := by
      have hratio : Complex.normSq c / (Complex.normSq c + 1) ≤ 1 :=
        (div_le_one hden).2 (by linarith [Complex.normSq_nonneg c])
      have hεw : 0 ≤ ε * w n := mul_nonneg hε.le (hw n)
      exact mul_le_mul_of_nonneg_right hratio hεw
    _ = ε * w n := one_mul _

theorem ScaledMassVanishing.finset_sum {B : OpAlmostRepresentation E}
    {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {I : Type} (s : Finset I)
    (x : I → ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : ∀ i ∈ s, ScaledMassVanishing B w (x i)) :
    ScaledMassVanishing B w (fun n ↦ ∑ i ∈ s, x i n) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro ε hε
      refine ⟨0, fun n _ ↦ ?_⟩
      simp only [Finset.sum_empty]
      rw [matMass_zero]
      exact mul_nonneg hε.le (hw n)
  | @insert i s hi ih =>
      simpa [Finset.sum_insert, hi] using
        (hx i (Finset.mem_insert_self i s)).add
          (ih fun j hj ↦ hx j (Finset.mem_insert_of_mem hj))

/-- Exact unitary conjugation preserves scaled mass nullity. -/
theorem ScaledMassVanishing.unitary_conjugate
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : ScaledMassVanishing B w x)
    (u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ) :
    ScaledMassVanishing B w (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) * x n *
        (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  intro ε hε
  obtain ⟨N, hN⟩ := hx ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [matMass_unitary_conj (u n).2]
  exact hN n hn

/-- At the dimension weight, scaled mass vanishing is exactly normalized
Hilbert--Schmidt vanishing. -/
theorem scaledMassVanishing_card_iff_hsSqVanishing
    {B : OpAlmostRepresentation E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ} :
    ScaledMassVanishing B (fun n ↦ (Fintype.card (B.model n) : ℝ)) x ↔
      HSSqVanishing B x := by
  have hcard : ∀ n, (0 : ℝ) < Fintype.card (B.model n) := by
    intro n
    exact_mod_cast B.modelNonempty n
  constructor
  · intro hx ε hε
    obtain ⟨N, hN⟩ := hx ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have h := hN n hn
    rw [hsNormSq, div_le_iff₀ (hcard n)]
    calc
      (∑ i : B.model n, ∑ j : B.model n, Complex.normSq (x n i j)) =
          matMass (x n) := rfl
      _ ≤ ε * Fintype.card (B.model n) := h
  · intro hx ε hε
    obtain ⟨N, hN⟩ := hx ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have h := hN n hn
    rw [hsNormSq, div_le_iff₀ (hcard n)] at h
    calc
      matMass (x n) =
          ∑ i : B.model n, ∑ j : B.model n, Complex.normSq (x n i j) := rfl
      _ ≤ ε * Fintype.card (B.model n) := h

/-! ## Scaled mass boundedness -/

/-- Frobenius mass `O(w n)`, the sector on which scaled transport operates. -/
def IsScaledMassBounded (B : OpAlmostRepresentation E) (w : ℕ → ℝ)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) : Prop :=
  ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ n, matMass (x n) ≤ Cm * w n

/-- The zero sequence is mass bounded at every nonnegative weight. -/
theorem isScaledMassBounded_zero (B : OpAlmostRepresentation E)
    (w : ℕ → ℝ) :
    IsScaledMassBounded B w (fun n ↦ (0 : Matrix (B.model n) (B.model n) ℂ)) := by
  refine ⟨0, le_refl 0, fun n ↦ ?_⟩
  rw [matMass_zero, zero_mul]

/-- Exact unitary conjugation preserves scaled mass boundedness. -/
theorem IsScaledMassBounded.unitary_conjugate
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsScaledMassBounded B w x)
    (u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ) :
    IsScaledMassBounded B w (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) * x n *
        (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  obtain ⟨Cm, hCm, hCx⟩ := hx
  refine ⟨Cm, hCm, fun n ↦ ?_⟩
  rw [matMass_unitary_conj (u n).2]
  exact hCx n

theorem IsScaledMassBounded.adjointSequence
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ} {g : E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsScaledMassBounded B w x) :
    IsScaledMassBounded B w
      (KazhdanAsymptoticCommutant.adjointSequence B g x) := by
  obtain ⟨Cm, hCm, hCx⟩ := hx
  refine ⟨Cm, hCm, fun n ↦ ?_⟩
  calc
    matMass (KazhdanAsymptoticCommutant.adjointSequence B g x n) =
        matMass ((B.map n g : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ) := rfl
    _ = matMass (x n) := matMass_unitary_conj (B.map n g).2 _
    _ ≤ Cm * w n := hCx n

theorem IsScaledMassBounded.coadjointSequence
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ} {g : E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsScaledMassBounded B w x) :
    IsScaledMassBounded B w
      (KazhdanAsymptoticCommutant.coadjointSequence B g x) := by
  obtain ⟨Cm, hCm, hCx⟩ := hx
  refine ⟨Cm, hCm, fun n ↦ ?_⟩
  have hU : (B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ ∈
      Matrix.unitaryGroup (B.model n) ℂ :=
    conjTranspose_mem_unitaryGroup (B.map n g).2
  have hconj : matMass
      ((B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
        ((B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ)ᴴ) =
      matMass (x n) :=
    matMass_unitary_conj hU _
  rw [Matrix.conjTranspose_conjTranspose] at hconj
  calc
    matMass (KazhdanAsymptoticCommutant.coadjointSequence B g x n) =
        matMass ((B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
          (B.map n g : Matrix (B.model n) (B.model n) ℂ)) := rfl
    _ = matMass (x n) := hconj
    _ ≤ Cm * w n := hCx n

/-- Operator-norm boundedness gives mass boundedness at the dimension
weight; the scaled theory at `w = card` therefore strictly extends the
normalized one. -/
theorem IsUniformlyBounded.isScaledMassBounded_card
    {B : OpAlmostRepresentation E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsUniformlyBounded B x) :
    IsScaledMassBounded B (fun n ↦ (Fintype.card (B.model n) : ℝ)) x := by
  obtain ⟨M, hM, hMx⟩ := hx
  refine ⟨M ^ 2, sq_nonneg M, fun n ↦ ?_⟩
  calc
    matMass (x n) ≤ Fintype.card (B.model n) * ‖x n‖ ^ 2 :=
      sum_normSq_le_card_mul_sq (B.model n) (x n)
    _ ≤ Fintype.card (B.model n) * M ^ 2 := by
      have hsq : ‖x n‖ ^ 2 ≤ M ^ 2 := by
        nlinarith [norm_nonneg (x n), hMx n]
      exact mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)
    _ = M ^ 2 * Fintype.card (B.model n) := mul_comm _ _

/-! ## The scaled asymptotic commutant -/

/-- A matrix sequence asymptotically centralizes the image of a homomorphism
at scale `w`. -/
def IsScaledAsymptoticCommutantOf {G : Type v} [Group G]
    (B : OpAlmostRepresentation E)
    (w : ℕ → ℝ) (iota : G →* E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) : Prop :=
  ∀ γ : G, ScaledMassVanishing B w (fun n ↦
    x n - (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ) *
      x n * (B.map n (iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ)

/-- The compression-core form of the scaled asymptotic commutant. -/
abbrev IsScaledAsymptoticCommutant {G : Type v} [Group G]
    (B : OpAlmostRepresentation E)
    (w : ℕ → ℝ) (C : KazhdanCompressionCore G E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ) : Prop :=
  IsScaledAsymptoticCommutantOf B w C.iota x

/-- The zero sequence lies in the scaled asymptotic commutant of every
homomorphism, at every nonnegative weight. -/
theorem isScaledAsymptoticCommutantOf_zero (B : OpAlmostRepresentation E)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (iota : Γ →* E) :
    IsScaledAsymptoticCommutantOf B w iota
      (fun n ↦ (0 : Matrix (B.model n) (B.model n) ℂ)) := by
  intro γ
  refine (scaledMassVanishing_zero B w hw).congr fun n ↦ ?_
  rw [mul_zero, zero_mul, sub_zero]

/-- Scaled-mass-equivalent sequences have the same scaled commutation
relations. -/
theorem IsScaledAsymptoticCommutantOf.congr_mass
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ} {iota : Γ →* E}
    {x y : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsScaledAsymptoticCommutantOf B w iota x)
    (hxy : ScaledMassVanishing B w (fun n ↦ x n - y n)) :
    IsScaledAsymptoticCommutantOf B w iota y := by
  intro gamma
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ :=
    fun n ↦ B.map n (iota gamma)
  have hconj := hxy.unitary_conjugate u
  have hsum := ((hx gamma).add hxy.neg).add hconj
  exact hsum.congr fun n ↦ by
    have hu : (u n : Matrix (B.model n) (B.model n) ℂ) *
        (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ = 1 :=
      Unitary.mul_star_self_of_mem (u n).2
    simp only [u]
    noncomm_ring [hu]

/-- Conjugating a mass-bounded sequence by operator-norm-equivalent
unitaries changes it by a scaled-mass-null sequence.  This is the scaled
replacement for the operator-norm conjugation maneuver: the operator-norm
bound on the sequence is replaced by its Frobenius mass bound. -/
theorem scaled_conjugation_massVanishing_of_opNormVanishing
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (u v : ∀ n, Matrix.unitaryGroup (B.model n) ℂ)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : IsScaledMassBounded B w x)
    (huv : OpNormVanishing B (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) - v n)) :
    ScaledMassVanishing B w (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) * x n *
          (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ -
        (v n : Matrix (B.model n) (B.model n) ℂ) * x n *
          (v n : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  obtain ⟨Cm, hCm, hCx⟩ := hbound
  intro ε hε
  have hden : 0 < 8 * (Cm + 1) := by positivity
  obtain ⟨N, hN⟩ := huv (Real.sqrt (ε / (8 * (Cm + 1))))
    (Real.sqrt_pos.2 (div_pos hε hden))
  refine ⟨N, fun n hn ↦ ?_⟩
  let U : Matrix (B.model n) (B.model n) ℂ := u n
  let V : Matrix (B.model n) (B.model n) ℂ := v n
  let X : Matrix (B.model n) (B.model n) ℂ := x n
  show matMass (U * X * Uᴴ - V * X * Vᴴ) ≤ ε * w n
  have hUVsq : ‖U - V‖ ^ 2 ≤ ε / (8 * (Cm + 1)) := by
    have h := hN n hn
    have hnn : 0 ≤ ‖U - V‖ := norm_nonneg _
    have hs : ‖U - V‖ ≤ Real.sqrt (ε / (8 * (Cm + 1))) := h
    calc
      ‖U - V‖ ^ 2 ≤ Real.sqrt (ε / (8 * (Cm + 1))) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (ε / (8 * (Cm + 1)))]
      _ = ε / (8 * (Cm + 1)) :=
        Real.sq_sqrt (le_of_lt (div_pos hε hden))
  have hsplit : U * X * Uᴴ - V * X * Vᴴ =
      (U - V) * X * Uᴴ + V * (X * (U - V)ᴴ) := by
    rw [Matrix.conjTranspose_sub]
    noncomm_ring
  have hterm1 : matMass ((U - V) * X * Uᴴ) ≤
      ‖U - V‖ ^ 2 * matMass X := by
    have hUright : Uᴴ * (Uᴴ)ᴴ = 1 := by
      rw [Matrix.conjTranspose_conjTranspose]
      have h := Matrix.mem_unitaryGroup_iff'.mp (u n).2
      rwa [Matrix.star_eq_conjTranspose] at h
    calc
      matMass ((U - V) * X * Uᴴ) =
          matMass ((U - V) * X) :=
        matMass_mul_right_of_mul_star_self hUright ((U - V) * X)
      _ ≤ ‖U - V‖ ^ 2 * matMass X := matMass_mul_le_left _ _
  have hterm2 : matMass (V * (X * (U - V)ᴴ)) ≤
      ‖U - V‖ ^ 2 * matMass X := by
    have hVleft : Vᴴ * V = 1 := by
      have h := Matrix.mem_unitaryGroup_iff'.mp (v n).2
      rwa [Matrix.star_eq_conjTranspose] at h
    calc
      matMass (V * (X * (U - V)ᴴ)) = matMass (X * (U - V)ᴴ) :=
        matMass_mul_left_of_star_mul_self hVleft _
      _ ≤ ‖(U - V)ᴴ‖ ^ 2 * matMass X := matMass_mul_le_right _ _
      _ = ‖U - V‖ ^ 2 * matMass X := by
        rw [← Matrix.star_eq_conjTranspose, norm_star]
  calc
    matMass (U * X * Uᴴ - V * X * Vᴴ) =
        matMass ((U - V) * X * Uᴴ + V * (X * (U - V)ᴴ)) := by
      rw [hsplit]
    _ ≤ 2 * matMass ((U - V) * X * Uᴴ) +
        2 * matMass (V * (X * (U - V)ᴴ)) := matMass_add_le _ _
    _ ≤ 4 * (‖U - V‖ ^ 2 * matMass X) := by
      nlinarith [hterm1, hterm2, matMass_nonneg ((U - V) * X * Uᴴ),
        matMass_nonneg (V * (X * (U - V)ᴴ))]
    _ ≤ 4 * (ε / (8 * (Cm + 1)) * (Cm * w n)) := by
      have hmass := hCx n
      have hmassnn : 0 ≤ matMass X := matMass_nonneg X
      have hann : 0 ≤ ε / (8 * (Cm + 1)) := div_nonneg hε.le hden.le
      have h1 : 0 ≤ (ε / (8 * (Cm + 1)) - ‖U - V‖ ^ 2) * matMass X :=
        mul_nonneg (sub_nonneg.mpr hUVsq) hmassnn
      have h2 : 0 ≤ ε / (8 * (Cm + 1)) * (Cm * w n - matMass X) :=
        mul_nonneg hann (sub_nonneg.mpr hmass)
      nlinarith [h1, h2]
    _ ≤ ε * w n := by
      have hεw : 0 ≤ ε * w n := mul_nonneg hε.le (hw n)
      have hratio : 4 * Cm / (8 * (Cm + 1)) ≤ 1 := by
        rw [div_le_one hden]
        linarith
      have hE : 4 * (ε / (8 * (Cm + 1)) * (Cm * w n)) =
          ε * w n * (4 * Cm / (8 * (Cm + 1))) := by
        field_simp
      rw [hE]
      calc
        ε * w n * (4 * Cm / (8 * (Cm + 1))) ≤ ε * w n * 1 :=
          mul_le_mul_of_nonneg_left hratio hεw
        _ = ε * w n := mul_one _

/-! ## Group-law bookkeeping for the scaled adjoint action -/

theorem scaled_adjointSequence_mul
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (g h : E) (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : IsScaledMassBounded B w x) :
    ScaledMassVanishing B w (fun n ↦
      adjointSequence B (g * h) x n -
        adjointSequence B g (adjointSequence B h x) n) := by
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦ B.map n (g * h)
  let v : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦
    ⟨(B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n h,
      mul_mem (B.map n g).2 (B.map n h).2⟩
  simpa [adjointSequence, u, v, Matrix.mul_assoc] using
    scaled_conjugation_massVanishing_of_opNormVanishing hw u v x hbound
      (multiplicativeDefect_vanishing B g h)

theorem scaled_coadjointSequence_mul
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (g h : E) (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : IsScaledMassBounded B w x) :
    ScaledMassVanishing B w (fun n ↦
      coadjointSequence B (g * h) x n -
        coadjointSequence B h (coadjointSequence B g x) n) := by
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦
    ⟨(B.map n (g * h) : Matrix (B.model n) (B.model n) ℂ)ᴴ,
      conjTranspose_mem_unitaryGroup (B.map n (g * h)).2⟩
  let v : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦
    ⟨((B.map n g : Matrix (B.model n) (B.model n) ℂ) * B.map n h)ᴴ,
      conjTranspose_mem_unitaryGroup (mul_mem (B.map n g).2 (B.map n h).2)⟩
  have hdef := OpNormVanishing.conjTranspose
    (B := B) (multiplicativeDefect_vanishing B g h)
  have hdef' : OpNormVanishing B (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) - v n) := by
    simpa only [u, v, Matrix.conjTranspose_sub] using hdef
  simpa [coadjointSequence, u, v, Matrix.conjTranspose_mul,
    Matrix.mul_assoc] using
    scaled_conjugation_massVanishing_of_opNormVanishing hw u v x hbound hdef'

theorem scaled_adjointSequence_inv
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (g : E) (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : IsScaledMassBounded B w x) :
    ScaledMassVanishing B w (fun n ↦
      adjointSequence B g⁻¹ x n - coadjointSequence B g x n) := by
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦ B.map n g⁻¹
  let v : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦
    ⟨(B.map n g : Matrix (B.model n) (B.model n) ℂ)ᴴ,
      conjTranspose_mem_unitaryGroup (B.map n g).2⟩
  simpa [adjointSequence, coadjointSequence, u, v] using
    scaled_conjugation_massVanishing_of_opNormVanishing hw u v x hbound
      (map_inv_vanishing B g)

theorem scaled_coadjointSequence_inv
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (g : E) (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : IsScaledMassBounded B w x) :
    ScaledMassVanishing B w (fun n ↦
      coadjointSequence B g⁻¹ x n - adjointSequence B g x n) := by
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦
    ⟨(B.map n g⁻¹ : Matrix (B.model n) (B.model n) ℂ)ᴴ,
      conjTranspose_mem_unitaryGroup (B.map n g⁻¹).2⟩
  let v : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦ B.map n g
  have hdef := OpNormVanishing.conjTranspose (B := B) (map_inv_vanishing B g)
  have hdef' : OpNormVanishing B (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) - v n) := by
    simpa only [u, v, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose] using hdef
  simpa [adjointSequence, coadjointSequence, u, v] using
    scaled_conjugation_massVanishing_of_opNormVanishing hw u v x hbound hdef'

theorem scaled_adjointSequence_one
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : IsScaledMassBounded B w x) :
    ScaledMassVanishing B w (fun n ↦ adjointSequence B 1 x n - x n) := by
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦ B.map n 1
  let v : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦ ⟨1, by simp⟩
  simpa [adjointSequence, u, v] using
    scaled_conjugation_massVanishing_of_opNormVanishing hw u v x hbound
      (map_one_vanishing B)

theorem scaled_coadjointSequence_one
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : IsScaledMassBounded B w x) :
    ScaledMassVanishing B w (fun n ↦ coadjointSequence B 1 x n - x n) := by
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦
    ⟨(B.map n 1 : Matrix (B.model n) (B.model n) ℂ)ᴴ,
      conjTranspose_mem_unitaryGroup (B.map n 1).2⟩
  let v : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦ ⟨1, by simp⟩
  have hdef := OpNormVanishing.conjTranspose (B := B) (map_one_vanishing B)
  have hdef' : OpNormVanishing B (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) - v n) := by
    simpa only [u, v, Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
      using hdef
  simpa [coadjointSequence, u, v] using
    scaled_conjugation_massVanishing_of_opNormVanishing hw u v x hbound hdef'

/-! ## The scaled stabilizer subgroup -/

/-- Elements whose adjoint and inverse-adjoint actions preserve every
mass-bounded scaled asymptotic-commutant sequence. -/
def scaledCommutantStabilizer (B : OpAlmostRepresentation E)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (iota : Γ →* E) : Subgroup E where
  carrier := {g | ∀ x, IsScaledMassBounded B w x →
    IsScaledAsymptoticCommutantOf B w iota x →
    IsScaledAsymptoticCommutantOf B w iota (adjointSequence B g x) ∧
      IsScaledAsymptoticCommutantOf B w iota (coadjointSequence B g x)}
  one_mem' := by
    intro x hbound hx
    exact ⟨IsScaledAsymptoticCommutantOf.congr_mass hx
        (scaled_adjointSequence_one hw x hbound).sub_symm,
      IsScaledAsymptoticCommutantOf.congr_mass hx
        (scaled_coadjointSequence_one hw x hbound).sub_symm⟩
  mul_mem' := by
    intro g h hg hh x hbound hx
    have hhx := hh x hbound hx
    have hforward := hg (adjointSequence B h x)
      (IsScaledMassBounded.adjointSequence hbound) hhx.1
    have hbackward := hh (coadjointSequence B g x)
      (IsScaledMassBounded.coadjointSequence hbound)
      (hg x hbound hx).2
    exact ⟨IsScaledAsymptoticCommutantOf.congr_mass hforward.1
        (scaled_adjointSequence_mul hw g h x hbound).sub_symm,
      IsScaledAsymptoticCommutantOf.congr_mass hbackward.2
        (scaled_coadjointSequence_mul hw g h x hbound).sub_symm⟩
  inv_mem' := by
    intro g hg x hbound hx
    have hgx := hg x hbound hx
    exact ⟨IsScaledAsymptoticCommutantOf.congr_mass hgx.2
        (scaled_adjointSequence_inv hw g x hbound).sub_symm,
      IsScaledAsymptoticCommutantOf.congr_mass hgx.1
        (scaled_coadjointSequence_inv hw g x hbound).sub_symm⟩

/-! ## The scaled Laplacian and spectral capture -/

/-- Conjugating the reverse displacement by the implementing unitary turns
it into the negative forward displacement, at every scale. -/
theorem scaled_reverse_massVanishing
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ}
    {C : KazhdanCompressionCore Γ E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsScaledAsymptoticCommutant B w C x) (γ : Γ) :
    ScaledMassVanishing B w (fun n ↦
      x n - (B.map n (C.iota γ) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
        x n * B.map n (C.iota γ)) := by
  let u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦ B.map n (C.iota γ)
  have h := (hx γ).neg.unitary_conjugate (fun n ↦
    ⟨(u n : Matrix (B.model n) (B.model n) ℂ)ᴴ,
      conjTranspose_mem_unitaryGroup (u n).2⟩)
  exact h.congr fun n ↦ by
    have huu : (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ * u n = 1 :=
      Unitary.star_mul_self_of_mem (u n).2
    have hux : (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ *
        ((u n : Matrix (B.model n) (B.model n) ℂ) * x n) = x n := by
      rw [← Matrix.mul_assoc, huu, one_mul]
    change (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ *
          (-(x n - (u n : Matrix (B.model n) (B.model n) ℂ) * x n *
            (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ)) *
          ((u n : Matrix (B.model n) (B.model n) ℂ)ᴴ)ᴴ =
        x n - (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n * u n
    rw [Matrix.conjTranspose_conjTranspose]
    noncomm_ring
    rw [huu, mul_one, hux]

/-- The Hermitian Kazhdan-average residual of a scaled asymptotic-commutant
sequence is scaled-mass null. -/
theorem scaled_laplacian_massVanishing
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    {C : KazhdanCompressionCore Γ E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsScaledAsymptoticCommutant B w C x)
    (S : Finset Γ) (_hone : 1 ∈ S) :
    ScaledMassVanishing B w (fun n ↦
      (2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S,
        ((x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
            x n * (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
          (x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
            x n * B.map n (C.iota s))))) := by
  have hsum : ScaledMassVanishing B w (fun n ↦ ∑ s ∈ S,
      ((x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
          x n * (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
        (x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
          x n * B.map n (C.iota s)))) := by
    apply ScaledMassVanishing.finset_sum hw S
    intro s _
    exact (hx s).add (scaled_reverse_massVanishing hx s)
  exact ((hsum.smul hw (S.card : ℂ)⁻¹).smul hw (2 : ℂ)⁻¹)

/-- **Scaled spectral capture.**  A mass-bounded scaled asymptotic-commutant
sequence is eventually captured by the finite-stage Kazhdan corner, with
capture error measured against the weight rather than the dimension. -/
theorem scaled_capture_vanishing
    {B : OpAlmostRepresentation E} {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    {C : KazhdanCompressionCore Γ E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ}
    (hx : IsScaledAsymptoticCommutant B w C x)
    (hbound : IsScaledMassBounded B w x)
    {S : Finset Γ} (hone : 1 ∈ S) {θ : ℝ} (hθ : θ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      MarkedCompressionVectorChain.vecMass
        ((1 - cornerProjection B C S θ n) *ᵥ gammaRowVec B n (x n)) ≤
          ε * w n := by
  classical
  obtain ⟨Cm, hCm, hCx⟩ := hbound
  intro ε hε
  have hgap : 0 < 1 - θ := by linarith
  let η : ℝ := (1 - θ) * ε / (Cm + 1)
  have hden : 0 < Cm + 1 := by linarith
  have hη : 0 < η := div_pos (mul_pos hgap hε) hden
  obtain ⟨N, hN⟩ := scaled_laplacian_massVanishing hw hx S hone
    (η ^ 2) (sq_pos_of_pos hη)
  refine ⟨N, fun n hn ↦ ?_⟩
  let R : Matrix (B.model n) (B.model n) ℂ :=
    (2 : ℂ)⁻¹ • ((S.card : ℂ)⁻¹ • ∑ s ∈ S,
      ((x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ) *
          x n * (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ) +
        (x n - (B.map n (C.iota s) : Matrix (B.model n) (B.model n) ℂ)ᴴ *
          x n * B.map n (C.iota s))))
  let H := hermitianAverage (gammaAdjoint B C) S n
  let P := cornerProjection B C S θ n
  let ξ := gammaRowVec B n (x n)
  have hresidVec : ξ - H *ᵥ ξ = gammaRowVec B n R := by
    simpa [R, H, ξ] using matrix_laplacian_matVec B C S hone n (x n)
  have hR : matMass R ≤ η ^ 2 * w n := by
    simpa [R] using hN n hn
  have hresidMass :
      ∑ i : (gammaAdjoint B C).model n,
          Complex.normSq ((ξ - H *ᵥ ξ) i) ≤ η ^ 2 * w n := by
    rw [hresidVec, sum_normSq_gammaRowVec]
    exact hR
  have hxiMass :
      ∑ i : (gammaAdjoint B C).model n, Complex.normSq (ξ i) ≤
        Cm * w n := by
    rw [show ξ = gammaRowVec B n (x n) by rfl, sum_normSq_gammaRowVec]
    exact hCx n
  have henergy : (star ξ ⬝ᵥ (ξ - H *ᵥ ξ)).re ≤
      ((1 - θ) * ε) * w n := by
    have hamgm := re_star_dotProduct_le hη ξ (ξ - H *ᵥ ξ)
    calc
      (star ξ ⬝ᵥ (ξ - H *ᵥ ξ)).re ≤
          (2 : ℝ)⁻¹ *
            (η * ∑ i, Complex.normSq (ξ i) +
              η⁻¹ * ∑ i, Complex.normSq ((ξ - H *ᵥ ξ) i)) := hamgm
      _ ≤ (2 : ℝ)⁻¹ *
            (η * (Cm * w n) + η⁻¹ * (η ^ 2 * w n)) := by gcongr
      _ = (2 : ℝ)⁻¹ * ((Cm + 1) * η * w n) := by
        have hinv : η⁻¹ * (η ^ 2 * w n) = η * w n := by
          rw [sq]
          field_simp [hη.ne']
        rw [hinv]
        ring
      _ = (2 : ℝ)⁻¹ * ((1 - θ) * ε * w n) := by
        have hηval : (Cm + 1) * η = (1 - θ) * ε := by
          dsimp [η]
          field_simp [hden.ne']
        rw [hηval]
      _ ≤ ((1 - θ) * ε) * w n := by
        have hnn : 0 ≤ (1 - θ) * ε * w n :=
          mul_nonneg (mul_nonneg hgap.le hε.le) (hw n)
        linarith
  have hcapture := capture_vec H
    (by simpa [H, Matrix.IsHermitian, Matrix.star_eq_conjTranspose] using
      hermitianAverage_conjTranspose (gammaAdjoint B C) S n)
    θ 0 hθ.le (by norm_num)
    (by simpa [H] using norm_hermitianAverage_le_one (gammaAdjoint B C) S n) ξ
  have hbelow : spectralBelow H
      (hermitianAverage_conjTranspose (gammaAdjoint B C) S n) θ = 1 - P := rfl
  rw [hbelow, zero_mul, add_zero] at hcapture
  have hmul : (1 - θ) *
      MarkedCompressionVectorChain.vecMass ((1 - P) *ᵥ ξ) ≤
        (1 - θ) * (ε * w n) :=
    hcapture.trans (by simpa [mul_assoc] using henergy)
  exact le_of_mul_le_mul_left hmul hgap

/-! ## Scaled transport -/

private theorem scaled_transport_of_leakage
    (B : OpAlmostRepresentation E) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsScaledAsymptoticCommutant B w C x)
    (hbound : IsScaledMassBounded B w x)
    (S : Finset Γ) (kappa theta : ℝ)
    (hone : 1 ∈ S) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set Γ) = ⊤)
    (hkappaOne : kappa ≤ 1)
    (hpair : IsKazhdanPair.{0, 0} Γ S kappa)
    (htheta4 : 1 - kappa ^ 2 / (4 * S.card) < theta)
    (htheta1 : theta < 1)
    (u : ∀ n, Matrix.unitaryGroup (B.model n) ℂ)
    (hleak : ∀ epsilon : ℝ, 0 < epsilon → ∃ N, ∀ n ≥ N,
      ‖(1 - cornerProjection B C S theta n) *
        (adjointMatrixSequence B u n * cornerProjection B C S theta n *
          (adjointMatrixSequence B u n)ᴴ)‖ ≤ epsilon) :
    IsScaledAsymptoticCommutant B w C (fun n ↦
      (u n : Matrix (B.model n) (B.model n) ℂ) * x n *
        (u n : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  classical
  obtain ⟨Cm, hCm, hCx⟩ := hbound
  intro γ ε hε
  let q : ℝ := min 1 (ε / (40 * (Cm + 1)))
  have hden : 0 < 40 * (Cm + 1) := by positivity
  have hq : 0 < q := lt_min (by norm_num) (div_pos hε hden)
  obtain ⟨Nfix, hNfix⟩ := displacement_vanishing B C theta hpair hone
    hkappaOne hsymm hgen htheta4 γ q hq
  obtain ⟨Nrev, hNrev⟩ := hleak q hq
  obtain ⟨Ncap, hNcap⟩ := scaled_capture_vanishing hw hx ⟨Cm, hCm, hCx⟩
    hone htheta1 q hq
  refine ⟨max Nfix (max Nrev Ncap), fun n hn ↦ ?_⟩
  let Ua : Matrix (B.model n) (B.model n) ℂ := B.map n (C.iota γ)
  let Ut : Matrix (B.model n) (B.model n) ℂ := u n
  let X : Matrix (B.model n) (B.model n) ℂ := x n
  let P : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
    cornerProjection B C S theta n
  let Ta : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
    B.adjoint.map n (C.iota γ)
  let Tt : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
    adjointMatrixSequence B u n
  have hfix : ‖(Ta - 1) * P‖ ≤ q := by
    simpa [Ta, Ua, P, gammaAdjoint] using
      hNfix n ((le_max_left _ _).trans hn)
  have hrev : ‖(1 - P) * (Tt * P * Ttᴴ)‖ ≤ q := by
    simpa [Tt, P, Ut] using
      hNrev n ((le_max_left Nrev Ncap).trans
        ((le_max_right Nfix (max Nrev Ncap)).trans hn))
  have hcap := hNcap n ((le_max_right Nrev Ncap).trans
    ((le_max_right Nfix (max Nrev Ncap)).trans hn))
  have hchain := MarkedCompressionVectorChain.transported_displacement_le
    (Y := B.adjoint.model n) (B.adjoint.modelNonempty n)
    (cornerProjection_isOrthogonalProjection B C S theta n)
    (show Tt ∈ Matrix.unitaryGroup (B.adjoint.model n) ℂ by
      exact adjointMatrixSequence_mem_unitaryGroup B u n)
    (show Ta ∈ Matrix.unitaryGroup (B.adjoint.model n) ℂ by
      exact (B.adjoint.map n (C.iota γ)).2)
    hfix hrev hcap
  have hxmass : MarkedCompressionVectorChain.vecMass (gammaRowVec B n X) ≤
      Cm * w n := by
    rw [vecMass_gammaRowVec]
    exact hCx n
  have hqone : q ≤ 1 := min_le_left _ _
  have hqeps : q * (40 * (Cm + 1)) ≤ ε := by
    calc
      q * (40 * (Cm + 1)) ≤
          (ε / (40 * (Cm + 1))) * (40 * (Cm + 1)) := by
        gcongr
        exact min_le_right _ _
      _ = ε := by field_simp
  have hmass :
      MarkedCompressionVectorChain.vecMass
        (Ta *ᵥ (Tt *ᵥ gammaRowVec B n X) -
          Tt *ᵥ gammaRowVec B n X) ≤
        (2 * q ^ 2 + 16 * q ^ 2) *
            MarkedCompressionVectorChain.vecMass (gammaRowVec B n X) +
          16 * (q * w n) :=
    hchain
  have hmass' :
      MarkedCompressionVectorChain.vecMass
        (Ta *ᵥ (Tt *ᵥ gammaRowVec B n X) -
          Tt *ᵥ gammaRowVec B n X) ≤
        (18 * q ^ 2 * Cm + 16 * q) * w n := by
    calc
      _ ≤ (2 * q ^ 2 + 16 * q ^ 2) *
            MarkedCompressionVectorChain.vecMass (gammaRowVec B n X) +
          16 * (q * w n) := hmass
      _ ≤ (2 * q ^ 2 + 16 * q ^ 2) * (Cm * w n) + 16 * (q * w n) := by
        gcongr
      _ = (18 * q ^ 2 * Cm + 16 * q) * w n := by ring
  have hsmall : 18 * q ^ 2 * Cm + 16 * q ≤ ε := by
    calc
      18 * q ^ 2 * Cm + 16 * q ≤ q * (40 * (Cm + 1)) := by
        nlinarith [hCm, hq.le, hqone, mul_nonneg hq.le hCm,
          mul_nonneg (mul_nonneg hq.le hCm) (sub_nonneg.mpr hqone)]
      _ ≤ ε := hqeps
  let D : Matrix (B.model n) (B.model n) ℂ := Ut * X * Utᴴ
  let E' : Matrix (B.model n) (B.model n) ℂ := Ua * D * Uaᴴ
  have hTt : Tt *ᵥ gammaRowVec B n X = gammaRowVec B n D := by
    simpa [Tt, Ut, D] using
      adjointMatrixSequence_mulVec_gammaRowVec B u n X
  have hTa : Ta *ᵥ gammaRowVec B n D = gammaRowVec B n E' := by
    simpa [Ta, Ua, E', gammaAdjoint] using
      gammaAdjoint_mulVec_gammaRowVec B C n γ D
  have hvec : Ta *ᵥ (Tt *ᵥ gammaRowVec B n X) -
      Tt *ᵥ gammaRowVec B n X = gammaRowVec B n (E' - D) := by
    rw [hTt, hTa, ← gammaRowVec_sub]
  change matMass (Ut * X * Utᴴ - Ua * (Ut * X * Utᴴ) * Uaᴴ) ≤ ε * w n
  calc
    matMass (Ut * X * Utᴴ - Ua * (Ut * X * Utᴴ) * Uaᴴ) =
        MarkedCompressionVectorChain.vecMass
          (Ta *ᵥ (Tt *ᵥ gammaRowVec B n X) -
            Tt *ᵥ gammaRowVec B n X) := by
      rw [hvec, MarkedCompressionVectorChain.vecMass,
        sum_normSq_gammaRowVec]
      unfold matMass
      refine Finset.sum_congr rfl fun i _ ↦
        Finset.sum_congr rfl fun j _ ↦ ?_
      rw [show (Ut * X * Utᴴ - Ua * (Ut * X * Utᴴ) * Uaᴴ) i j =
          -((E' - D) i j) by simp [E', D],
        Complex.normSq_neg]
    _ ≤ (18 * q ^ 2 * Cm + 16 * q) * w n := hmass'
    _ ≤ ε * w n := mul_le_mul_of_nonneg_right hsmall (hw n)

/-- **Forward scaled Kazhdan transport.**  A one-sided compressor preserves
every mass-bounded scaled asymptotic-commutant sequence, at every
nonnegative weight. -/
theorem scaled_transport
    (B : OpAlmostRepresentation E) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsScaledAsymptoticCommutant B w C x)
    (hbound : IsScaledMassBounded B w x) :
    IsScaledAsymptoticCommutant B w C (fun n ↦
      (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) := by
  classical
  obtain ⟨S, kappa, hone, hsymm, hgen, hkappa, hkappaOne, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair
      C.kazhdan
  let theta : ℝ := ((1 - kappa ^ 2 / (4 * S.card)) + 1) / 2
  have htheta4 : 1 - kappa ^ 2 / (4 * S.card) < theta := by
    dsimp [theta]
    have hcard : 0 < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
    have : 0 < kappa ^ 2 / (4 * (S.card : ℝ)) := by positivity
    linarith
  have htheta1 : theta < 1 := by
    dsimp [theta]
    have hcard : 0 < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
    have : 0 < kappa ^ 2 / (4 * (S.card : ℝ)) := by positivity
    linarith
  apply scaled_transport_of_leakage B w hw C x hx hbound S kappa theta hone
    hsymm hgen hkappaOne hpair htheta4 htheta1 (fun n ↦ B.map n C.t)
  intro epsilon hepsilon
  simpa [movedProjection, adjointMatrixSequence] using
    one_sub_corner_mul_moved_vanishing B C theta hpair hone hkappaOne
      hsymm hgen htheta4 htheta1 epsilon hepsilon

/-- **Reverse scaled Kazhdan transport.**  The equal-rank projection flip
upgrades the one-sided compressor to invariance under the inverse adjoint
action, at every nonnegative weight. -/
theorem scaled_transport_star
    (B : OpAlmostRepresentation E) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsScaledAsymptoticCommutant B w C x)
    (hbound : IsScaledMassBounded B w x) :
    IsScaledAsymptoticCommutant B w C (fun n ↦
      (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) := by
  classical
  obtain ⟨S, kappa, hone, hsymm, hgen, hkappa, hkappaOne, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair
      C.kazhdan
  let theta : ℝ := ((1 - kappa ^ 2 / (4 * S.card)) + 1) / 2
  have htheta4 : 1 - kappa ^ 2 / (4 * S.card) < theta := by
    dsimp [theta]
    have hcard : 0 < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
    have : 0 < kappa ^ 2 / (4 * (S.card : ℝ)) := by positivity
    linarith
  have htheta1 : theta < 1 := by
    dsimp [theta]
    have hcard : 0 < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
    have : 0 < kappa ^ 2 / (4 * (S.card : ℝ)) := by positivity
    linarith
  let ustar : ∀ n, Matrix.unitaryGroup (B.model n) ℂ := fun n ↦
    ⟨(B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ,
      conjTranspose_mem_unitaryGroup (B.map n C.t).2⟩
  have hleak : ∀ epsilon : ℝ, 0 < epsilon → ∃ N, ∀ n ≥ N,
      ‖(1 - cornerProjection B C S theta n) *
        (adjointMatrixSequence B ustar n * cornerProjection B C S theta n *
          (adjointMatrixSequence B ustar n)ᴴ)‖ ≤ epsilon := by
    intro epsilon hepsilon
    obtain ⟨N, hN⟩ := one_sub_moved_mul_corner_vanishing B C theta hpair
      hone hkappaOne hsymm hgen htheta4 htheta1 epsilon hepsilon
    refine ⟨N, fun n hn ↦ ?_⟩
    let T : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
      conjDouble (B.map n C.t)
    let P : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ :=
      cornerProjection B C S theta n
    have hT : T ∈ Matrix.unitaryGroup (B.adjoint.model n) ℂ :=
      conjDouble_mem_unitaryGroup (B.map n C.t).2
    have hTstar : Tᴴ ∈ Matrix.unitaryGroup (B.adjoint.model n) ℂ :=
      conjTranspose_mem_unitaryGroup hT
    have hTstarT : Tᴴ * T = 1 := Unitary.star_mul_self_of_mem hT
    have hcancel : ∀ Y : Matrix (B.adjoint.model n) (B.adjoint.model n) ℂ,
        Tᴴ * (T * Y) = Y := by
      intro Y
      rw [← Matrix.mul_assoc, hTstarT, one_mul]
    have hraw : ‖(1 - T * P * Tᴴ) * P‖ ≤ epsilon := by
      simpa [T, P, movedProjection] using hN n hn
    have hfactor :
        (1 - P) * (Tᴴ * P * T) = Tᴴ * ((1 - T * P * Tᴴ) * P) * T := by
      noncomm_ring
      rw [hcancel]
    have htarget : ‖(1 - P) * (Tᴴ * P * T)‖ ≤ epsilon := by
      rw [hfactor, CStarRing.norm_mul_mem_unitary _ hT,
        CStarRing.norm_mem_unitary_mul _ hTstar]
      exact hraw
    simpa [T, P, ustar, adjointMatrixSequence,
      conjDouble_conjTranspose] using htarget
  have htransport := scaled_transport_of_leakage B w hw C x hx hbound S
    kappa theta hone hsymm hgen hkappaOne hpair htheta4 htheta1 ustar hleak
  simpa [ustar, Matrix.conjTranspose_conjTranspose] using htransport

/-- A one-sided compressor acts as a two-sided symmetry of the mass-bounded
scaled asymptotic commutant, at every nonnegative weight. -/
theorem scaled_transport_both :
    ∀ {Γ : Type} {E : Type u} [Group Γ] [Group E]
      (B : OpAlmostRepresentation E) (w : ℕ → ℝ) (_hw : ∀ n, 0 ≤ w n)
      (C : KazhdanCompressionCore Γ E)
      (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
      (_hx : IsScaledAsymptoticCommutant B w C x)
      (_hbound : IsScaledMassBounded B w x),
      IsScaledAsymptoticCommutant B w C (fun n ↦
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
            (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) ∧
        IsScaledAsymptoticCommutant B w C (fun n ↦
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
            (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) := by
  intro Γ E _ _ B w hw C x hx hbound
  exact ⟨scaled_transport B w hw C x hx hbound,
    scaled_transport_star B w hw C x hx hbound⟩

/-! ## The dimension weight

The superseded manuscript revision recorded, immediately after its weighted
transport theorem, that
the dimension weight `w n = d n` recovers the unscaled transport theorem with
the uniform operator-norm bound relaxed to mass boundedness.  The two halves of
that sentence are proved here: at the dimension weight the scaled commutant
*is* the normalized Hilbert--Schmidt commutant, and uniform operator-norm
boundedness is a strictly special case of mass boundedness at that weight
(`IsUniformlyBounded.isScaledMassBounded_card` above). -/

/-- At the dimension weight the scaled asymptotic commutant is literally the
normalized Hilbert--Schmidt asymptotic commutant of
`Sofic.KazhdanAsymptoticCommutant`: no estimate is involved, only the identity
`matMass = d n · hsNormSq`. -/
theorem isScaledAsymptoticCommutantOf_card_iff
    {B : OpAlmostRepresentation E} {iota : Γ →* E}
    {x : ∀ n, Matrix (B.model n) (B.model n) ℂ} :
    IsScaledAsymptoticCommutantOf B
        (fun n ↦ (Fintype.card (B.model n) : ℝ)) iota x ↔
      IsAsymptoticCommutantOf B iota x :=
  ⟨fun h γ ↦ scaledMassVanishing_card_iff_hsSqVanishing.mp (h γ),
    fun h γ ↦ scaledMassVanishing_card_iff_hsSqVanishing.mpr (h γ)⟩

/-- **The dimension weight recovers the transport theorem, with the bound
relaxed.**  Specializing the scaled theorem at `w n = d n` returns exactly the
conclusion of `KazhdanAsymptoticCommutant.transport_both` — the printed
Theorem 3.1 — but from Frobenius mass boundedness rather than from a uniform
operator-norm bound.  Together with `IsUniformlyBounded.isScaledMassBounded_card`
this is the manuscript's claim that the dimension weight is a special case of
the scaled theorem, and a strictly stronger one. -/
theorem transport_both_of_card_massBounded
    (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsAsymptoticCommutant B C x)
    (hbound : IsScaledMassBounded B
      (fun n ↦ (Fintype.card (B.model n) : ℝ)) x) :
    IsAsymptoticCommutant B C (fun n ↦
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) ∧
      IsAsymptoticCommutant B C (fun n ↦
        (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
          (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)) := by
  have hw : ∀ n, (0 : ℝ) ≤ (Fintype.card (B.model n) : ℝ) := fun n ↦
    Nat.cast_nonneg _
  obtain ⟨hfwd, hrev⟩ :=
    scaled_transport_both B (fun n ↦ (Fintype.card (B.model n) : ℝ)) hw C x
      (isScaledAsymptoticCommutantOf_card_iff.mpr hx) hbound
  exact ⟨isScaledAsymptoticCommutantOf_card_iff.mp hfwd,
    isScaledAsymptoticCommutantOf_card_iff.mp hrev⟩

/-- **The scaled theorem at `w n = d n` is Theorem 3.1.**  Closed form of the
manuscript's remark: for every ambient group, every operator-norm almost
representation and every compression datum, the dimension weight identifies the
scaled asymptotic commutant with the normalized Hilbert--Schmidt one, uniform
operator-norm boundedness implies mass boundedness at that weight, and the
scaled transport theorem therefore yields the two-sided conclusion of
Theorem 3.1 from the weaker bound. -/
theorem manuscriptDimensionWeightRecovery :
    ∀ {Γ : Type} {E : Type u} [Group Γ] [Group E]
      (B : OpAlmostRepresentation E) (C : KazhdanCompressionCore Γ E)
      (x : ∀ n, Matrix (B.model n) (B.model n) ℂ),
      (IsScaledAsymptoticCommutant B
          (fun n ↦ (Fintype.card (B.model n) : ℝ)) C x ↔
        IsAsymptoticCommutant B C x) ∧
      (IsUniformlyBounded B x →
        IsScaledMassBounded B (fun n ↦ (Fintype.card (B.model n) : ℝ)) x) ∧
      (IsAsymptoticCommutant B C x →
        IsScaledMassBounded B (fun n ↦ (Fintype.card (B.model n) : ℝ)) x →
        IsAsymptoticCommutant B C (fun n ↦
            (B.map n C.t : Matrix (B.model n) (B.model n) ℂ) * x n *
              (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ) ∧
          IsAsymptoticCommutant B C (fun n ↦
            (B.map n C.t : Matrix (B.model n) (B.model n) ℂ)ᴴ * x n *
              (B.map n C.t : Matrix (B.model n) (B.model n) ℂ))) := by
  intro Γ E _ _ B C x
  exact ⟨isScaledAsymptoticCommutantOf_card_iff,
    fun hb ↦ IsUniformlyBounded.isScaledMassBounded_card hb,
    fun hx hbound ↦ transport_both_of_card_massBounded B C x hx hbound⟩

/-! ## All compressors -/

/-- Every one-sided compressor acts in both directions on the mass-bounded
scaled asymptotic commutant. -/
theorem compressionSet_scaled_transport_both
    (B : OpAlmostRepresentation E) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (iota : Γ →* E) (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hx : IsScaledAsymptoticCommutantOf B w iota x)
    (hbound : IsScaledMassBounded B w x)
    {s : E} (hs : s ∈ compressionSet iota.range) :
    IsScaledAsymptoticCommutantOf B w iota (adjointSequence B s x) ∧
      IsScaledAsymptoticCommutantOf B w iota (coadjointSequence B s x) := by
  let C := coreOfCompressor iota hkazhdan s hs
  have hxC : IsScaledAsymptoticCommutant B w C x := by
    change IsScaledAsymptoticCommutantOf B w iota x
    exact hx
  have htransport := scaled_transport_both B w hw C x hxC hbound
  change IsScaledAsymptoticCommutantOf B w C.iota
      (adjointSequence B C.t x) ∧
    IsScaledAsymptoticCommutantOf B w C.iota
      (coadjointSequence B C.t x) at htransport
  change IsScaledAsymptoticCommutantOf B w iota (adjointSequence B s x) ∧
    IsScaledAsymptoticCommutantOf B w iota (coadjointSequence B s x)
  exact htransport

/-- Every one-sided compressor belongs to the scaled stabilizer. -/
theorem compressionSet_subset_scaledCommutantStabilizer
    (B : OpAlmostRepresentation E) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (iota : Γ →* E) (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ) :
    compressionSet iota.range ⊆
      scaledCommutantStabilizer B w hw iota := by
  intro s hs x hbound hx
  exact compressionSet_scaled_transport_both B w hw iota hkazhdan
    x hx hbound hs

/-- **All-compressors scaled Kazhdan transport.**  The group generated by
every one-sided compressor acts as a two-sided symmetry of the entire
mass-bounded scaled asymptotic commutant, for every nonnegative weight
sequence simultaneously.  Taking the weight to be the matrix dimension
recovers the normalized-Hilbert--Schmidt transport theorem; taking it to be
a rank scale gives the arbitrary-rescaling matricial Mautner statement. -/
theorem compressionGroup_le_scaledCommutantStabilizer
    (B : OpAlmostRepresentation E) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (iota : Γ →* E) (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ) :
    compressionGroup iota.range ≤
      scaledCommutantStabilizer B w hw iota := by
  rw [compressionGroup, Subgroup.closure_le]
  exact compressionSet_subset_scaledCommutantStabilizer B w hw iota hkazhdan

/-- Pointwise form of the all-compressors scaled transport theorem. -/
theorem compressionGroup_scaled_transport_both
    {Γ₀ : Type} {E₀ : Type u} [Group Γ₀] [Group E₀]
    (B : OpAlmostRepresentation E₀) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (iota : Γ₀ →* E₀) (hkazhdan : HasKazhdanPropertyT.{0, 0} Γ₀)
    {g : E₀} (hg : g ∈ compressionGroup iota.range)
    (x : ∀ n, Matrix (B.model n) (B.model n) ℂ)
    (hbound : IsScaledMassBounded B w x)
    (hx : IsScaledAsymptoticCommutantOf B w iota x) :
    IsScaledAsymptoticCommutantOf B w iota (adjointSequence B g x) ∧
      IsScaledAsymptoticCommutantOf B w iota (coadjointSequence B g x) :=
  compressionGroup_le_scaledCommutantStabilizer B w hw iota hkazhdan hg
    x hbound hx

end ScaledKazhdanTransport
end GroupApproximation
