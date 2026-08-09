import NonsoficGroupsExist.Sofic.KazhdanCornerCompression
import NonsoficGroupsExist.Sofic.HyperlinearUltraproductBridge

/-!
# Finite moving-corner models

This file realizes the complementary spectral cutoff as an honest smaller
matrix algebra.  The coordinates are the eigenvectors whose Hermitian-average
eigenvalue is at most the cutoff.  Principal compression is contractive in
the matrix `ℓ²` operator norm, and the almost-reducing estimates from
`KazhdanCornerCompression` therefore pass to these smaller matrices.
-/

namespace NonsoficGroupsExist
namespace KazhdanCornerMatrices

open Matrix
open scoped Matrix.Norms.L2Operator

/-! ## Principal compression -/

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The moving spectral coordinates below a threshold. -/
def MovingIndex (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (t : ℝ) :=
  {i : Y // hH.eigenvalues i ≤ t}

noncomputable instance (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (t : ℝ) :
    Fintype (MovingIndex H hH t) := by
  letI : Finite (MovingIndex H hH t) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance (H : Matrix Y Y ℂ) (hH : H.IsHermitian) (t : ℝ) :
    DecidableEq (MovingIndex H hH t) := Classical.decEq _

/-- Principal matrix block on a decidable family of coordinates. -/
def coordinateBlock (p q : Y → Prop) [DecidablePred p] [DecidablePred q]
    (C : Matrix Y Y ℂ) : Matrix {i // p i} {i // q i} ℂ :=
  C.toBlock p q

/-- Principal matrix block on a decidable family of coordinates. -/
def principalBlock (p : Y → Prop) [DecidablePred p] (C : Matrix Y Y ℂ) :
    Matrix {i // p i} {i // p i} ℂ := coordinateBlock p p C

/-- A zero extension from a coordinate family to the ambient coordinates. -/
def extendByZero (p : Y → Prop) [DecidablePred p]
    (x : {i // p i} → ℂ) : Y → ℂ :=
  fun i ↦ if hi : p i then x ⟨i, hi⟩ else 0

omit [Fintype Y] [DecidableEq Y] in
theorem extendByZero_apply (p : Y → Prop) [DecidablePred p]
    (x : {i // p i} → ℂ) (i : {i // p i}) :
    extendByZero p x i = x i := by
  simp [extendByZero, i.2]

omit [DecidableEq Y] in
/-- A principal block acts as the restriction of the ambient matrix acting
on the zero extension. -/
theorem principalBlock_mulVec (p : Y → Prop) [DecidablePred p]
    (C : Matrix Y Y ℂ) (x : {i // p i} → ℂ) (i : {i // p i}) :
    (principalBlock p C *ᵥ x) i = (C *ᵥ extendByZero p x) i := by
  classical
  simp only [principalBlock, coordinateBlock, Matrix.toBlock_apply,
    Matrix.mulVec, dotProduct]
  rw [← Fintype.sum_subtype_add_sum_subtype p
    (fun j ↦ C i j * extendByZero p x j)]
  have hpos : (∑ j : {j // p j}, C i j * extendByZero p x j) =
      ∑ j : {j // p j}, C i j * x j := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [extendByZero, j.2]
  have hneg : (∑ j : {j // ¬p j}, C i j * extendByZero p x j) = 0 := by
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    simp [extendByZero, j.2]
  rw [hpos, hneg, add_zero]

/-- Squared Euclidean norm, in entrywise form, for an arbitrary finite
coordinate type. -/
theorem euclidean_norm_sq_general {Z : Type*} [Fintype Z]
    (w : Z → ℂ) :
    ‖(EuclideanSpace.equiv Z ℂ).symm w‖ ^ 2 =
      ∑ i : Z, Complex.normSq (w i) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun i _ ↦ (Complex.normSq_eq_norm_sq _).symm

/-- General finite-type version of the operator-norm vector criterion. -/
theorem l2_opNorm_le_of_sum_normSq_general
    {R Z : Type*} [Fintype R] [Fintype Z] [DecidableEq R] [DecidableEq Z]
    (C : Matrix R Z ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x : Z → ℂ, ∑ i : R, Complex.normSq ((C *ᵥ x) i) ≤
      M ^ 2 * ∑ i : Z, Complex.normSq (x i)) :
    ‖C‖ ≤ M := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x ↦ ?_
  have hL : ‖(EuclideanSpace.equiv R ℂ).symm (C *ᵥ x)‖ ^ 2 =
      ∑ i : R, Complex.normSq ((C *ᵥ x) i) :=
    euclidean_norm_sq_general _
  have hR : ‖(EuclideanSpace.equiv Z ℂ).symm x‖ ^ 2 =
      ∑ i : Z, Complex.normSq (x i) := euclidean_norm_sq_general _
  have hval : ‖(LinearEquiv.trans
      (Matrix.toEuclideanLin (𝕜 := ℂ) (m := R) (n := Z))
      LinearMap.toContinuousLinearMap C) x‖ =
      ‖(EuclideanSpace.equiv R ℂ).symm (C *ᵥ x)‖ := rfl
  rw [hval]
  have hsquares : ‖(EuclideanSpace.equiv R ℂ).symm (C *ᵥ x)‖ ^ 2 ≤
      (M * ‖x‖) ^ 2 := by
    rw [hL, mul_pow]
    have hxx : ‖x‖ ^ 2 = ∑ i : Z, Complex.normSq (x i) := hR
    rw [hxx]
    exact h x
  have hleft : 0 ≤ ‖(EuclideanSpace.equiv R ℂ).symm (C *ᵥ x)‖ :=
    norm_nonneg _
  have hright : 0 ≤ M * ‖x‖ := mul_nonneg hM (norm_nonneg _)
  nlinarith

/-- The operator norm bounds every matrix-vector product, for an arbitrary
finite coordinate type. -/
theorem sum_normSq_mulVec_le_general {Z : Type*} [Fintype Z]
    [DecidableEq Z] (C : Matrix Z Z ℂ) (x : Z → ℂ) :
    ∑ i : Z, Complex.normSq ((C *ᵥ x) i) ≤
      ‖C‖ ^ 2 * ∑ i : Z, Complex.normSq (x i) := by
  have h : ‖(EuclideanSpace.equiv Z ℂ).symm (C *ᵥ x)‖ ≤
      ‖C‖ * ‖(EuclideanSpace.equiv Z ℂ).symm x‖ :=
    Matrix.l2_opNorm_mulVec C ((EuclideanSpace.equiv Z ℂ).symm x)
  have hL := euclidean_norm_sq_general (C *ᵥ x)
  have hR := euclidean_norm_sq_general x
  have hsquare : ‖(EuclideanSpace.equiv Z ℂ).symm (C *ᵥ x)‖ ^ 2 ≤
      (‖C‖ * ‖(EuclideanSpace.equiv Z ℂ).symm x‖) ^ 2 := by
    nlinarith [norm_nonneg ((EuclideanSpace.equiv Z ℂ).symm (C *ᵥ x)),
      norm_nonneg C, norm_nonneg ((EuclideanSpace.equiv Z ℂ).symm x)]
  calc
    ∑ i : Z, Complex.normSq ((C *ᵥ x) i) =
        ‖(EuclideanSpace.equiv Z ℂ).symm (C *ᵥ x)‖ ^ 2 := hL.symm
    _ ≤ (‖C‖ * ‖(EuclideanSpace.equiv Z ℂ).symm x‖) ^ 2 := hsquare
    _ = ‖C‖ ^ 2 * ∑ i : Z, Complex.normSq (x i) := by
      rw [mul_pow, hR]

/-- Principal compression cannot increase the matrix operator norm. -/
theorem norm_principalBlock_le (p : Y → Prop) [DecidablePred p]
    (C : Matrix Y Y ℂ) : ‖principalBlock p C‖ ≤ ‖C‖ := by
  classical
  refine l2_opNorm_le_of_sum_normSq_general (principalBlock p C)
    (norm_nonneg C) fun x ↦ ?_
  let xhat := extendByZero p x
  have hout :
      ∑ i : {i // p i}, Complex.normSq ((principalBlock p C *ᵥ x) i) ≤
        ∑ i : Y, Complex.normSq ((C *ᵥ xhat) i) := by
    rw [← Fintype.sum_subtype_add_sum_subtype p
      (fun i ↦ Complex.normSq ((C *ᵥ xhat) i))]
    simp only [principalBlock_mulVec]
    exact le_add_of_nonneg_right
      (Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _)
  have hin : ∑ i : Y, Complex.normSq (xhat i) =
      ∑ i : {i // p i}, Complex.normSq (x i) := by
    rw [← Fintype.sum_subtype_add_sum_subtype p
      (fun i ↦ Complex.normSq (xhat i))]
    have hpos : (∑ i : {i // p i}, Complex.normSq (xhat i)) =
        ∑ i : {i // p i}, Complex.normSq (x i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp [xhat, extendByZero, i.2]
    have hneg : (∑ i : {i // ¬p i}, Complex.normSq (xhat i)) = 0 := by
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      simp [xhat, extendByZero, i.2]
    rw [hpos, hneg, add_zero]
  calc
    ∑ i : {i // p i}, Complex.normSq ((principalBlock p C *ᵥ x) i)
        ≤ ∑ i : Y, Complex.normSq ((C *ᵥ xhat) i) := hout
    _ ≤ ‖C‖ ^ 2 * ∑ i : Y, Complex.normSq (xhat i) := by
      exact sum_normSq_mulVec_le_general C xhat
    _ = ‖C‖ ^ 2 * ∑ i : {i // p i}, Complex.normSq (x i) := by
      rw [hin]

omit [DecidableEq Y] in
/-- A rectangular coordinate block acts as the corresponding restriction
after zero extension in the column coordinates. -/
theorem coordinateBlock_mulVec (p q : Y → Prop)
    [DecidablePred p] [DecidablePred q] (C : Matrix Y Y ℂ)
    (x : {i // q i} → ℂ) (i : {i // p i}) :
    (coordinateBlock p q C *ᵥ x) i =
      (C *ᵥ extendByZero q x) i := by
  classical
  simp only [coordinateBlock, Matrix.toBlock_apply, Matrix.mulVec, dotProduct]
  rw [← Fintype.sum_subtype_add_sum_subtype q
    (fun j ↦ C i j * extendByZero q x j)]
  have hpos : (∑ j : {j // q j}, C i j * extendByZero q x j) =
      ∑ j : {j // q j}, C i j * x j := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [extendByZero, j.2]
  have hneg : (∑ j : {j // ¬q j}, C i j * extendByZero q x j) = 0 := by
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    simp [extendByZero, j.2]
  rw [hpos, hneg, add_zero]

/-- Every rectangular coordinate block is an operator-norm contraction of
the ambient matrix. -/
theorem norm_coordinateBlock_le (p q : Y → Prop)
    [DecidablePred p] [DecidablePred q] (C : Matrix Y Y ℂ) :
    ‖coordinateBlock p q C‖ ≤ ‖C‖ := by
  classical
  refine l2_opNorm_le_of_sum_normSq_general (coordinateBlock p q C)
    (norm_nonneg C) fun x ↦ ?_
  let xhat := extendByZero q x
  have hout :
      ∑ i : {i // p i}, Complex.normSq ((coordinateBlock p q C *ᵥ x) i) ≤
        ∑ i : Y, Complex.normSq ((C *ᵥ xhat) i) := by
    rw [← Fintype.sum_subtype_add_sum_subtype p
      (fun i ↦ Complex.normSq ((C *ᵥ xhat) i))]
    simp only [coordinateBlock_mulVec]
    exact le_add_of_nonneg_right
      (Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _)
  have hin : ∑ i : Y, Complex.normSq (xhat i) =
      ∑ i : {i // q i}, Complex.normSq (x i) := by
    rw [← Fintype.sum_subtype_add_sum_subtype q
      (fun i ↦ Complex.normSq (xhat i))]
    have hpos : (∑ i : {i // q i}, Complex.normSq (xhat i)) =
        ∑ i : {i // q i}, Complex.normSq (x i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      simp [xhat, extendByZero, i.2]
    have hneg : (∑ i : {i // ¬q i}, Complex.normSq (xhat i)) = 0 := by
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      simp [xhat, extendByZero, i.2]
    rw [hpos, hneg, add_zero]
  calc
    ∑ i : {i // p i}, Complex.normSq ((coordinateBlock p q C *ᵥ x) i)
        ≤ ∑ i : Y, Complex.normSq ((C *ᵥ xhat) i) := hout
    _ ≤ ‖C‖ ^ 2 * ∑ i : Y, Complex.normSq (xhat i) :=
      sum_normSq_mulVec_le_general C xhat
    _ = ‖C‖ ^ 2 * ∑ i : {i // q i}, Complex.normSq (x i) := by
      rw [hin]

omit [Fintype Y] [DecidableEq Y] in
@[simp] theorem principalBlock_conjTranspose (p : Y → Prop)
    [DecidablePred p] (C : Matrix Y Y ℂ) :
    (principalBlock p C)ᴴ = principalBlock p Cᴴ := by
  ext i j
  rfl

omit [Fintype Y] [DecidableEq Y] in
@[simp] theorem principalBlock_sub (p : Y → Prop) [DecidablePred p]
    (C D : Matrix Y Y ℂ) :
    principalBlock p (C - D) = principalBlock p C - principalBlock p D := by
  rfl

omit [Fintype Y] in
@[simp] theorem principalBlock_one (p : Y → Prop) [DecidablePred p] :
    principalBlock p (1 : Matrix Y Y ℂ) = 1 := by
  ext i j
  simp [principalBlock, coordinateBlock, Matrix.toBlock_apply,
    Matrix.one_apply, Subtype.ext_iff]

omit [DecidableEq Y] in
/-- Multiplication splits into the retained intermediate coordinates and the
off-diagonal cross term. -/
theorem principalBlock_mul_eq_add_cross (p : Y → Prop) [DecidablePred p]
    (C D : Matrix Y Y ℂ) :
    principalBlock p (C * D) =
      principalBlock p C * principalBlock p D +
        coordinateBlock p (fun i ↦ ¬p i) C *
          coordinateBlock (fun i ↦ ¬p i) p D := by
  simpa only [principalBlock, coordinateBlock] using
    Matrix.toBlock_mul_eq_add p p p C D

/-- A block between disjoint coordinate families is bounded by the residual
on its column family. -/
theorem norm_coordinateBlock_disjoint_le_residual
    (p q : Y → Prop) [DecidablePred p] [DecidablePred q]
    (hdisj : ∀ i, p i → q i → False) (C : Matrix Y Y ℂ) :
    ‖coordinateBlock p q C‖ ≤
      ‖(C - 1) * Matrix.diagonal (fun i ↦ if q i then (1 : ℂ) else 0)‖ := by
  have heq : coordinateBlock p q C = coordinateBlock p q
      ((C - 1) * Matrix.diagonal (fun i ↦ if q i then (1 : ℂ) else 0)) := by
    classical
    ext i j
    by_cases hij : (i : Y) = j
    · exact False.elim (hdisj i i.2 (hij ▸ j.2))
    · simp [coordinateBlock, Matrix.toBlock_apply, hij, j.2]
  rw [heq]
  exact norm_coordinateBlock_le p q _

/-! ## Weak-MF moving coordinates -/

section WeakMF

variable {G : Type} [Group G]

/-- The finite-stage Hermitian average, abbreviated for the moving-corner
definitions. -/
noncomputable def movingHermitianAverage (A : WeakMFApproximation G)
    (S : Finset G) (n : ℕ) : Matrix (A.model n) (A.model n) ℂ :=
  hermitianAverage A S n

/-- The Hermitian proof used by the moving-coordinate type. -/
theorem movingHermitianAverage_isHermitian (A : WeakMFApproximation G)
    (S : Finset G) (n : ℕ) :
    (movingHermitianAverage A S n).IsHermitian :=
  hermitianAverage_conjTranspose A S n

/-- The honest finite coordinate type of the moving spectral corner. -/
abbrev WeakMFMovingIndex (A : WeakMFApproximation G) (S : Finset G)
    (t : ℝ) (n : ℕ) :=
  MovingIndex (movingHermitianAverage A S n)
    (movingHermitianAverage_isHermitian A S n) t

/-- A finite moving-corner matrix model. -/
noncomputable def weakMFMovingModel (A : WeakMFApproximation G)
    (S : Finset G) (t : ℝ) (n : ℕ) : FiniteModel :=
  ⟨WeakMFMovingIndex A S t n, inferInstance, Classical.decEq _⟩

/-- Conjugate a microstate into the eigenbasis of the Hermitian average. -/
noncomputable def eigenbasisMicrostate (A : WeakMFApproximation G)
    (S : Finset G) (n : ℕ) (g : G) :
    Matrix (A.model n) (A.model n) ℂ :=
  let U : Matrix (A.model n) (A.model n) ℂ :=
    (movingHermitianAverage_isHermitian A S n).eigenvectorUnitary
  Uᴴ * (A.map n g : Matrix (A.model n) (A.model n) ℂ) * U

/-- Principal compression of a weak-MF microstate to the moving eigenspace. -/
noncomputable def movingCompression (A : WeakMFApproximation G)
    (S : Finset G) (t : ℝ) (n : ℕ) (g : G) :
    Matrix (weakMFMovingModel A S t n) (weakMFMovingModel A S t n) ℂ :=
  principalBlock
    (fun i ↦ (movingHermitianAverage_isHermitian A S n).eigenvalues i ≤ t)
    (eigenbasisMicrostate A S n g)

/-- If every Hermitian eigenvalue lies above the threshold, the top spectral
cutoff is the identity. -/
theorem spectralAbove_eq_one_of_forall_lt (H : Matrix Y Y ℂ)
    (hH : H.IsHermitian) (t : ℝ) (h : ∀ i, t < hH.eigenvalues i) :
    spectralAbove H hH t = 1 := by
  unfold spectralAbove
  simp_rw [if_pos (h _)]
  rw [show Matrix.diagonal (fun _ : Y ↦ (1 : ℂ)) = 1 by ext i j; simp]
  rw [Matrix.mul_one]
  exact Unitary.mul_star_self_of_mem hH.eigenvectorUnitary.2

/-- The moving corner is eventually nonzero.  If it vanished at arbitrarily
late stages, the top cutoff would be the identity there; all-element top
displacement and the identity defect would then contradict weak-MF
separation. -/
theorem eventually_nonempty_weakMFMovingIndex [Nontrivial G]
    {Q : Finset G} {epsilon : ℝ}
    (hQ : IsKazhdanPair.{0, 0} G Q epsilon)
    (S : Finset G) (hQS : Q ⊆ S) (hone : 1 ∈ S)
    (hepsilonOne : epsilon ≤ 1) (hsymm : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (A : WeakMFApproximation G) {t : ℝ}
    (ht : 1 - epsilon ^ 2 / (4 * S.card) < t) :
    ∃ N, ∀ n ≥ N, Nonempty (WeakMFMovingIndex A S t n) := by
  classical
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hg1 : g ≠ 1 := hg
  have hdisp := topSpectralDisplacement_vanishing_of_generates
    hQ S hQS hone hepsilonOne hsymm hgen A ht g
  obtain ⟨Nd, hNd⟩ := hdisp (A.separation / 4) (by
    linarith [A.separation_pos])
  obtain ⟨N1, hN1⟩ := map_one_vanishing A (A.separation / 4) (by
    linarith [A.separation_pos])
  obtain ⟨Ns, hNs⟩ := A.separatedEventually g 1 hg1
  refine ⟨max (max Nd N1) Ns, fun n hn ↦ ?_⟩
  by_contra hempty
  have hall : ∀ i : A.model n,
      t < (movingHermitianAverage_isHermitian A S n).eigenvalues i := by
    intro i
    exact lt_of_not_ge fun hi ↦
      hempty ⟨⟨i, hi⟩⟩
  have hP : spectralAbove (hermitianAverage A S n)
      (hermitianAverage_conjTranspose A S n) t = 1 :=
    spectralAbove_eq_one_of_forall_lt _ _ _ hall
  have hNdle : Nd ≤ n :=
    (le_max_left Nd N1).trans (le_max_left (max Nd N1) Ns) |>.trans hn
  have hN1le : N1 ≤ n :=
    (le_max_right Nd N1).trans (le_max_left (max Nd N1) Ns) |>.trans hn
  have hd := hNd n hNdle
  have h1 := hN1 n hN1le
  have hs := hNs n ((le_max_right _ _).trans hn)
  change ‖((A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1) *
    spectralAbove (hermitianAverage A S n)
      (hermitianAverage_conjTranspose A S n) t‖ ≤ A.separation / 4 at hd
  rw [hP, Matrix.mul_one] at hd
  have hcontra : A.separation < A.separation := calc
    A.separation ≤
        ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ) - A.map n 1‖ := hs
    _ ≤ ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1‖ +
          ‖(A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1‖ := by
      rw [show (A.map n g : Matrix (A.model n) (A.model n) ℂ) - A.map n 1 =
        ((A.map n g : Matrix (A.model n) (A.model n) ℂ) - 1) -
          ((A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1) by abel]
      exact norm_sub_le _ _
    _ ≤ A.separation / 4 + A.separation / 4 := add_le_add hd h1
    _ < A.separation := by linarith [A.separation_pos]
  exact (lt_irrefl _ hcontra)

end WeakMF

end KazhdanCornerMatrices
end NonsoficGroupsExist
