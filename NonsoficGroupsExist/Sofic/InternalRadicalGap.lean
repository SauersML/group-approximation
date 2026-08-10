import NonsoficGroupsExist.Sofic.HyperlinearResidualDetector
import NonsoficGroupsExist.Sofic.KazhdanCornerDiagonal

/-!
# Normal Kazhdan corners inside weak-MF groups

This file develops the analytic bridge from an operator-norm approximation
of an ambient group to a tracial corner detected inside a normal
property-`(T)` subgroup.  Unlike the ordinary Kazhdan-corner construction,
the finite spectral set need not generate the ambient group.  Normality will
instead force its fixed-space projection to be ambient-invariant.

No permanence or representation theorem is taken as an input: the ambient
matrix corner is constructed from the given weak-MF approximation.
-/

namespace NonsoficGroupsExist
namespace InternalRadicalGap

open Matrix
open scoped Matrix.Norms.L2Operator

variable {H : Type} [Group H]

/-- A rectangular block is controlled by a diagonally row-scaled residual
when every retained row has a uniform gap from zero. -/
theorem norm_coordinateBlock_le_inv_mul_of_diagonal_gap
    {Y : Type} [Fintype Y] [DecidableEq Y]
    (p q : Y → Prop) [DecidablePred p] [DecidablePred q]
    (d : Y → ℂ) (W : Matrix Y Y ℂ) (c : ℝ) (hc : 0 < c)
    (hd : ∀ i, p i → c ≤ ‖d i‖) :
    ‖KazhdanCornerMatrices.coordinateBlock p q W‖ ≤
      c⁻¹ * ‖KazhdanCornerMatrices.coordinateBlock p q
        (Matrix.diagonal d * W)‖ := by
  classical
  let Dinv : Matrix {i // p i} {i // p i} ℂ :=
    Matrix.diagonal fun i ↦ (d i)⁻¹
  let R : Matrix {i // p i} {i // q i} ℂ :=
    KazhdanCornerMatrices.coordinateBlock p q (Matrix.diagonal d * W)
  have hdne (i : {i // p i}) : d i ≠ 0 := by
    intro hzero
    have := hd i i.property
    simp [hzero] at this
    linarith
  have hfactor :
      KazhdanCornerMatrices.coordinateBlock p q W = Dinv * R := by
    ext i j
    simp [Dinv, R, KazhdanCornerMatrices.coordinateBlock,
      Matrix.toBlock_apply, hdne i]
  have hDinv : ‖Dinv‖ ≤ c⁻¹ := by
    rw [Dinv, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hc.le)).2 fun i ↦ ?_
    rw [norm_inv]
    exact inv_le_inv₀ hc (hd i i.property)
  rw [hfactor]
  calc
    ‖Dinv * R‖ ≤ ‖Dinv‖ * ‖R‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ c⁻¹ * ‖R‖ := mul_le_mul_of_nonneg_right hDinv (norm_nonneg R)

/-- Finite spectral data for a prescribed ambient weak-MF approximation,
restricted to a property-`(T)` subgroup. -/
structure Setup (A : WeakMFApproximation H) (N : Subgroup H) where
  S : Finset N
  epsilon : ℝ
  one_mem : 1 ∈ S
  symmetric : ∀ g ∈ S, g⁻¹ ∈ S
  generates : Subgroup.closure (S : Set N) = ⊤
  epsilon_pos : 0 < epsilon
  epsilon_le_one : epsilon ≤ 1
  kazhdan : IsKazhdanPair.{0, 0} N S epsilon
  cutoff : ℝ
  gap_lt_cutoff : 1 - epsilon ^ 2 / (4 * S.card) < cutoff
  cutoff_lt_one : cutoff < 1

/-- Property `(T)` supplies normal-corner spectral data for the *given*
ambient approximation.  No second approximation is chosen. -/
theorem exists_setup (A : WeakMFApproximation H) (N : Subgroup H)
    (hT : HasKazhdanPropertyT.{0, 0} N) : Nonempty (Setup A N) := by
  classical
  obtain ⟨S, epsilon, hone, hsymm, hgen, hepsilon, hepsilonOne, hpair⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair hT
  have hcardNat : 0 < S.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hcardNat
  have hgap : 0 < epsilon ^ 2 / (4 * (S.card : ℝ)) :=
    div_pos (sq_pos_of_pos hepsilon) (mul_pos (by norm_num) hcard)
  let c : ℝ := 1 - epsilon ^ 2 / (4 * S.card)
  let t : ℝ := (c + 1) / 2
  have hct : c < t := by dsimp [c, t]; linarith
  have htOne : t < 1 := by dsimp [c, t]; linarith
  exact ⟨{
    S := S
    epsilon := epsilon
    one_mem := hone
    symmetric := hsymm
    generates := hgen
    epsilon_pos := hepsilon
    epsilon_le_one := hepsilonOne
    kazhdan := hpair
    cutoff := t
    gap_lt_cutoff := hct
    cutoff_lt_one := htOne }⟩

/-- Restrict the given ambient weak-MF approximation to the subgroup.  Its
finite matrix carriers are definitionally the ambient carriers. -/
abbrev restrictedApproximation (A : WeakMFApproximation H) (N : Subgroup H) :
    WeakMFApproximation N :=
  A.comap N.subtype Subtype.val_injective

/-- Every subgroup element asymptotically fixes the retained top spectral
subspace.  Generation is used only inside the subgroup; no ambient
generation hypothesis is needed. -/
theorem subgroupTopSpectralDisplacement_vanishing
    (A : WeakMFApproximation H) (N : Subgroup H) (D : Setup A N) (x : N) :
    KazhdanCornerMatrices.OpNormVanishing
      (restrictedApproximation A N)
      (fun n ↦ KazhdanCornerMatrices.topSpectralDisplacement
        (restrictedApproximation A N) D.S D.cutoff n x) := by
  apply KazhdanCornerMatrices.topSpectralDisplacement_vanishing_of_mem_closure
    D.kazhdan D.S (by rfl) D.one_mem D.epsilon_le_one D.symmetric
    (restrictedApproximation A N) D.gap_lt_cutoff
  rw [D.generates]
  exact Subgroup.mem_top x

/-- Conjugation by an ambient element, regarded as an element of a normal
subgroup. -/
def normalConjugate (N : Subgroup H) [N.Normal] (g : H) (x : N) : N :=
  ⟨g⁻¹ * x * g, Subgroup.Normal.conj_mem' inferInstance x x.property g⟩

@[simp]
theorem normalConjugate_coe (N : Subgroup H) [N.Normal] (g : H) (x : N) :
    (normalConjugate N g x : H) = g⁻¹ * x * g :=
  rfl

/-- Normality converts subgroup top-corner invariance into approximate
invariance of an ambient translate of that corner. -/
theorem subgroup_displacement_mul_ambient_top_vanishing
    (A : WeakMFApproximation H) (N : Subgroup H) [N.Normal]
    (D : Setup A N) (g : H) (s : N) :
    KazhdanCornerMatrices.OpNormVanishing A (fun n ↦
      ((A.map n (s : H) : Matrix (A.model n) (A.model n) ℂ) - 1) *
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          KazhdanCornerMatrices.spectralAbove
            (KazhdanCornerMatrices.hermitianAverage
              (restrictedApproximation A N) D.S n)
            (KazhdanCornerMatrices.hermitianAverage_conjTranspose
              (restrictedApproximation A N) D.S n)
            D.cutoff) := by
  let x : N := normalConjugate N g s
  let P : ∀ n, Matrix (A.model n) (A.model n) ℂ := fun n ↦
    KazhdanCornerMatrices.spectralAbove
      (KazhdanCornerMatrices.hermitianAverage
        (restrictedApproximation A N) D.S n)
      (KazhdanCornerMatrices.hermitianAverage_conjTranspose
        (restrictedApproximation A N) D.S n)
      D.cutoff
  have hP : ∀ n, ‖P n‖ ≤ 1 := fun n ↦
    KazhdanCornerMatrices.norm_spectralAbove_le_one _ _ _
  have hsg := (KazhdanCornerMatrices.multiplicativeDefect_vanishing
    A (s : H) g).mul_right_of_norm_le_one P hP
  have hgx := (KazhdanCornerMatrices.multiplicativeDefect_vanishing
    A g (x : H)).mul_right_of_norm_le_one P hP
  have hx := (subgroupTopSpectralDisplacement_vanishing A N D x).mul_left_of_norm_le_one
    (fun n ↦ (A.map n g : Matrix (A.model n) (A.model n) ℂ))
    (fun n ↦ (CStarRing.norm_of_mem_unitary (A.map n g).2).le)
  have htotal := hx.add hgx |>.sub hsg
  exact htotal.congr fun n ↦ by
    have hgroup : (s : H) * g = g * (x : H) := by
      simp only [x, normalConjugate_coe]
      simp [mul_assoc]
    simp only [P, KazhdanCornerMatrices.topSpectralDisplacement] at htotal ⊢
    rw [hgroup]
    noncomm_ring

/-- The subgroup orbit average acts asymptotically as the identity on every
ambient translate of the retained top corner. -/
theorem matrixAverage_sub_one_mul_ambient_top_vanishing
    (A : WeakMFApproximation H) (N : Subgroup H) [N.Normal]
    (D : Setup A N) (g : H) :
    KazhdanCornerMatrices.OpNormVanishing A (fun n ↦
      (KazhdanCornerMatrices.matrixAverage
          (restrictedApproximation A N) D.S n - 1) *
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          KazhdanCornerMatrices.spectralAbove
            (KazhdanCornerMatrices.hermitianAverage
              (restrictedApproximation A N) D.S n)
            (KazhdanCornerMatrices.hermitianAverage_conjTranspose
              (restrictedApproximation A N) D.S n)
            D.cutoff) := by
  classical
  let P : ∀ n, Matrix (A.model n) (A.model n) ℂ := fun n ↦
    KazhdanCornerMatrices.spectralAbove
      (KazhdanCornerMatrices.hermitianAverage
        (restrictedApproximation A N) D.S n)
      (KazhdanCornerMatrices.hermitianAverage_conjTranspose
        (restrictedApproximation A N) D.S n)
      D.cutoff
  let X : N → ∀ n, Matrix (A.model n) (A.model n) ℂ := fun s n ↦
    ((A.map n (s : H) : Matrix (A.model n) (A.model n) ℂ) - 1) *
      (A.map n g : Matrix (A.model n) (A.model n) ℂ) * P n
  have hsum := KazhdanCornerMatrices.OpNormVanishing.finset_sum D.S X
    (fun s _ ↦ subgroup_displacement_mul_ambient_top_vanishing A N D g s)
  have hscaled := hsum.smul (((D.S.card : ℂ)⁻¹))
  have hcard : (D.S.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr ⟨1, D.one_mem⟩)
  exact hscaled.congr fun n ↦ by
    change ((D.S.card : ℂ)⁻¹) •
        (∑ s ∈ D.S,
          ((A.map n (s : H) : Matrix (A.model n) (A.model n) ℂ) - 1) *
            (A.map n g : Matrix (A.model n) (A.model n) ℂ) * P n) = _
    rw [KazhdanCornerMatrices.matrixAverage]
    have hones : ((D.S.card : ℂ)⁻¹) •
        (∑ _s ∈ D.S, (1 : Matrix (A.model n) (A.model n) ℂ)) = 1 := by
      ext i j
      simp [hcard]
    rw [show (∑ s ∈ D.S,
          ((A.map n (s : H) : Matrix (A.model n) (A.model n) ℂ) - 1) *
            (A.map n g : Matrix (A.model n) (A.model n) ℂ) * P n) =
        ((∑ s ∈ D.S,
          (A.map n (s : H) : Matrix (A.model n) (A.model n) ℂ)) -
            ∑ _s ∈ D.S, 1) *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) * P n by
      simp_rw [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      noncomm_ring]
    rw [smul_mul_assoc, smul_mul_assoc, smul_sub, hones]

/-- Replacing the weak-MF orbit average by its exact Hermitian part preserves
ambient top-corner invariance. -/
theorem hermitianAverage_sub_one_mul_ambient_top_vanishing
    (A : WeakMFApproximation H) (N : Subgroup H) [N.Normal]
    (D : Setup A N) (g : H) :
    KazhdanCornerMatrices.OpNormVanishing A (fun n ↦
      (KazhdanCornerMatrices.hermitianAverage
          (restrictedApproximation A N) D.S n - 1) *
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          KazhdanCornerMatrices.spectralAbove
            (KazhdanCornerMatrices.hermitianAverage
              (restrictedApproximation A N) D.S n)
            (KazhdanCornerMatrices.hermitianAverage_conjTranspose
              (restrictedApproximation A N) D.S n)
            D.cutoff) := by
  let P : ∀ n, Matrix (A.model n) (A.model n) ℂ := fun n ↦
    KazhdanCornerMatrices.spectralAbove
      (KazhdanCornerMatrices.hermitianAverage
        (restrictedApproximation A N) D.S n)
      (KazhdanCornerMatrices.hermitianAverage_conjTranspose
        (restrictedApproximation A N) D.S n)
      D.cutoff
  let GP : ∀ n, Matrix (A.model n) (A.model n) ℂ := fun n ↦
    (A.map n g : Matrix (A.model n) (A.model n) ℂ) * P n
  have hGP : ∀ n, ‖GP n‖ ≤ 1 := fun n ↦ by
    calc
      ‖GP n‖ ≤ ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ)‖ * ‖P n‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul
        (CStarRing.norm_of_mem_unitary (A.map n g).2).le
        (KazhdanCornerMatrices.norm_spectralAbove_le_one _ _ _)
        (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have havg := matrixAverage_sub_one_mul_ambient_top_vanishing A N D g
  have hdiff := (KazhdanCornerMatrices.matrixAverage_sub_hermitian_vanishing
    (restrictedApproximation A N) D.S D.symmetric).neg.mul_right_of_norm_le_one GP hGP
  have htotal := hdiff.add havg
  exact htotal.congr fun n ↦ by
    simp only [GP, P]
    noncomm_ring

/-- The subgroup moving-coordinate type cut out inside the ambient matrix
model. -/
noncomputable abbrev MovingIndex (A : WeakMFApproximation H)
    (N : Subgroup H) (D : Setup A N) (n : ℕ) :=
  KazhdanCornerMatrices.WeakMFMovingIndex
    (restrictedApproximation A N) D.S D.cutoff n

/-- The subgroup spectral compression of an ambient element.  This is the
matrix whose asymptotic multiplicativity will follow from normality. -/
noncomputable def ambientEigenbasisMicrostate (A : WeakMFApproximation H)
    (N : Subgroup H) (D : Setup A N) (n : ℕ) (g : H) :
    Matrix (A.model n) (A.model n) ℂ :=
  let hAvg := KazhdanCornerMatrices.movingHermitianAverage_isHermitian
    (restrictedApproximation A N) D.S n
  let U : Matrix (A.model n) (A.model n) ℂ := hAvg.eigenvectorUnitary
  Uᴴ *
    (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
      U

/-- Ambient eigenbasis conjugation preserves unitarity exactly. -/
theorem ambientEigenbasisMicrostate_mem_unitaryGroup
    (A : WeakMFApproximation H) (N : Subgroup H) (D : Setup A N)
    (n : ℕ) (g : H) :
    ambientEigenbasisMicrostate A N D n g ∈
      Matrix.unitaryGroup (A.model n) ℂ := by
  let hAvg := KazhdanCornerMatrices.movingHermitianAverage_isHermitian
    (restrictedApproximation A N) D.S n
  let U : Matrix (A.model n) (A.model n) ℂ := hAvg.eigenvectorUnitary
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup (A.model n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hAvg.eigenvectorUnitary.2
  change Uᴴ * (A.map n g : Matrix (A.model n) (A.model n) ℂ) * U ∈
    Matrix.unitaryGroup (A.model n) ℂ
  exact mul_mem (mul_mem hUstar (A.map n g).2) hAvg.eigenvectorUnitary.2

/-- A uniform spectral gap controls the ambient moving-to-top block by the
Hermitian invariance residual. -/
theorem norm_ambientMovingToTopBlock_le_residual
    (A : WeakMFApproximation H) (N : Subgroup H) (D : Setup A N)
    (n : ℕ) (g : H) :
    ‖KazhdanCornerMatrices.coordinateBlock
        (KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n)
        (fun i ↦ ¬KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n i)
        (ambientEigenbasisMicrostate A N D n g)‖ ≤
      (1 - D.cutoff)⁻¹ *
        ‖(KazhdanCornerMatrices.hermitianAverage
              (restrictedApproximation A N) D.S n - 1) *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
            KazhdanCornerMatrices.spectralAbove
              (KazhdanCornerMatrices.hermitianAverage
                (restrictedApproximation A N) D.S n)
              (KazhdanCornerMatrices.hermitianAverage_conjTranspose
                (restrictedApproximation A N) D.S n)
              D.cutoff‖ := by
  classical
  let hAvg := KazhdanCornerMatrices.movingHermitianAverage_isHermitian
    (restrictedApproximation A N) D.S n
  let U : Matrix (A.model n) (A.model n) ℂ := hAvg.eigenvectorUnitary
  let L : Matrix (A.model n) (A.model n) ℂ :=
    Matrix.diagonal (fun i ↦ (hAvg.eigenvalues i : ℂ))
  let d : A.model n → ℂ := fun i ↦ (hAvg.eigenvalues i : ℂ) - 1
  let p : A.model n → Prop := fun i ↦ hAvg.eigenvalues i ≤ D.cutoff
  let q : A.model n → Prop := fun i ↦ ¬p i
  let W : Matrix (A.model n) (A.model n) ℂ :=
    ambientEigenbasisMicrostate A N D n g
  let Dtop : Matrix (A.model n) (A.model n) ℂ :=
    Matrix.diagonal (fun i ↦ if D.cutoff < hAvg.eigenvalues i then 1 else 0)
  let R : Matrix (A.model n) (A.model n) ℂ :=
    (KazhdanCornerMatrices.hermitianAverage
          (restrictedApproximation A N) D.S n - 1) *
      (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
        KazhdanCornerMatrices.spectralAbove
          (KazhdanCornerMatrices.hermitianAverage
            (restrictedApproximation A N) D.S n)
          (KazhdanCornerMatrices.hermitianAverage_conjTranspose
            (restrictedApproximation A N) D.S n)
          D.cutoff
  have hc : 0 < 1 - D.cutoff := by linarith [D.cutoff_lt_one]
  have hd : ∀ i, p i → 1 - D.cutoff ≤ ‖d i‖ := by
    intro i hi
    rw [show d i = ((hAvg.eigenvalues i - 1 : ℝ) : ℂ) by
      simp [d]]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith [hi])]
    linarith [hi]
  have hgap := norm_coordinateBlock_le_inv_mul_of_diagonal_gap
    p q d W (1 - D.cutoff) hc hd
  have hdiag : Matrix.diagonal d = L - 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [d, L]
    · simp [d, L, hij]
  have hUU : Uᴴ * U = 1 :=
    Unitary.star_mul_self_of_mem hAvg.eigenvectorUnitary.2
  have hUUstar : U * Uᴴ = 1 :=
    Unitary.mul_star_self_of_mem hAvg.eigenvectorUnitary.2
  have hHdiag :
      KazhdanCornerMatrices.hermitianAverage
          (restrictedApproximation A N) D.S n = U * L * Uᴴ := by
    exact hAvg.spectral_theorem
  have hPdiag :
      KazhdanCornerMatrices.spectralAbove
          (KazhdanCornerMatrices.hermitianAverage
            (restrictedApproximation A N) D.S n)
          (KazhdanCornerMatrices.hermitianAverage_conjTranspose
            (restrictedApproximation A N) D.S n)
          D.cutoff = U * Dtop * Uᴴ := by
    rfl
  have hconj : Uᴴ * R * U = (L - 1) * W * Dtop := by
    simp only [R, W, ambientEigenbasisMicrostate]
    rw [hHdiag, hPdiag]
    rw [show U * L * Uᴴ - 1 = U * (L - 1) * Uᴴ by
      rw [show (1 : Matrix (A.model n) (A.model n) ℂ) = U * Uᴴ by
        exact hUUstar.symm]
      noncomm_ring]
    rw [hUU]
    noncomm_ring
  have hblockD :
      KazhdanCornerMatrices.coordinateBlock p q ((L - 1) * W) =
        KazhdanCornerMatrices.coordinateBlock p q ((L - 1) * W * Dtop) := by
    ext i j
    have hj : D.cutoff < hAvg.eigenvalues j := lt_of_not_ge j.property
    simp [KazhdanCornerMatrices.coordinateBlock, Matrix.toBlock_apply,
      Dtop, hj, Matrix.mul_diagonal]
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup (A.model n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact hUU
  change ‖KazhdanCornerMatrices.coordinateBlock p q W‖ ≤ _
  calc
    ‖KazhdanCornerMatrices.coordinateBlock p q W‖ ≤
        (1 - D.cutoff)⁻¹ *
          ‖KazhdanCornerMatrices.coordinateBlock p q
            (Matrix.diagonal d * W)‖ := hgap
    _ = (1 - D.cutoff)⁻¹ *
          ‖KazhdanCornerMatrices.coordinateBlock p q ((L - 1) * W * Dtop)‖ := by
      rw [hdiag, hblockD]
    _ ≤ (1 - D.cutoff)⁻¹ * ‖Uᴴ * R * U‖ := by
      rw [hconj]
      exact mul_le_mul_of_nonneg_left
        (KazhdanCornerMatrices.norm_coordinateBlock_le p q _)
        (inv_nonneg.mpr hc.le)
    _ = (1 - D.cutoff)⁻¹ * ‖R‖ := by
      rw [KazhdanCornerMatrices.norm_unitary_conjugate hUstar]

/-- Normality and the subgroup spectral gap make the ambient moving-to-top
off-diagonal block vanish in operator norm. -/
theorem ambientMovingToTopBlock_vanishing
    (A : WeakMFApproximation H) (N : Subgroup H) [N.Normal]
    (D : Setup A N) (g : H) :
    KazhdanCornerMatrices.OpNormVanishing A (fun n ↦
      KazhdanCornerMatrices.coordinateBlock
        (KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n)
        (fun i ↦ ¬KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n i)
        (ambientEigenbasisMicrostate A N D n g)) := by
  have hres := hermitianAverage_sub_one_mul_ambient_top_vanishing A N D g
  intro eta heta
  have hgap : 0 < 1 - D.cutoff := by linarith [D.cutoff_lt_one]
  obtain ⟨stage, hstage⟩ := hres (eta * (1 - D.cutoff))
    (mul_pos heta hgap)
  refine ⟨stage, fun n hn ↦ ?_⟩
  calc
    ‖KazhdanCornerMatrices.coordinateBlock
        (KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n)
        (fun i ↦ ¬KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n i)
        (ambientEigenbasisMicrostate A N D n g)‖ ≤
      (1 - D.cutoff)⁻¹ *
        ‖(KazhdanCornerMatrices.hermitianAverage
              (restrictedApproximation A N) D.S n - 1) *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
            KazhdanCornerMatrices.spectralAbove
              (KazhdanCornerMatrices.hermitianAverage
                (restrictedApproximation A N) D.S n)
              (KazhdanCornerMatrices.hermitianAverage_conjTranspose
                (restrictedApproximation A N) D.S n)
              D.cutoff‖ :=
        norm_ambientMovingToTopBlock_le_residual A N D n g
    _ ≤ (1 - D.cutoff)⁻¹ * (eta * (1 - D.cutoff)) :=
      mul_le_mul_of_nonneg_left (hstage n hn) (inv_nonneg.mpr hgap.le)
    _ = eta := by field_simp

/-- The opposite ambient off-diagonal block also vanishes, by applying the
moving-to-top estimate to the inverse microstate. -/
theorem ambientTopToMovingBlock_vanishing
    (A : WeakMFApproximation H) (N : Subgroup H) [N.Normal]
    (D : Setup A N) (g : H) :
    KazhdanCornerMatrices.OpNormVanishing A (fun n ↦
      KazhdanCornerMatrices.coordinateBlock
        (fun i ↦ ¬KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n i)
        (KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n)
        (ambientEigenbasisMicrostate A N D n g)) := by
  intro eta heta
  obtain ⟨Nmove, hmove⟩ := ambientMovingToTopBlock_vanishing A N D g⁻¹
    (eta / 2) (by linarith)
  obtain ⟨Ninv, hinv⟩ := KazhdanCornerMatrices.map_inv_vanishing A g
    (eta / 2) (by linarith)
  refine ⟨max Nmove Ninv, fun n hn ↦ ?_⟩
  classical
  let p := KazhdanCornerMatrices.movingPredicate
    (restrictedApproximation A N) D.S D.cutoff n
  let hAvg := KazhdanCornerMatrices.movingHermitianAverage_isHermitian
    (restrictedApproximation A N) D.S n
  let U : Matrix (A.model n) (A.model n) ℂ := hAvg.eigenvectorUnitary
  let Wstar : Matrix (A.model n) (A.model n) ℂ :=
    (ambientEigenbasisMicrostate A N D n g)ᴴ
  let Winv : Matrix (A.model n) (A.model n) ℂ :=
    ambientEigenbasisMicrostate A N D n g⁻¹
  have hblockStar :
      ‖KazhdanCornerMatrices.coordinateBlock (fun i ↦ ¬p i) p
          (ambientEigenbasisMicrostate A N D n g)‖ =
        ‖KazhdanCornerMatrices.coordinateBlock p (fun i ↦ ¬p i) Wstar‖ := by
    rw [← KazhdanCornerMatrices.coordinateBlock_conjTranspose]
    exact (Matrix.l2_opNorm_conjTranspose
      (KazhdanCornerMatrices.coordinateBlock (fun i ↦ ¬p i) p
        (ambientEigenbasisMicrostate A N D n g))).symm
  have hdiff : Wstar - Winv =
      Uᴴ * ((A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ -
        (A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ)) * U := by
    simp only [Wstar, Winv, ambientEigenbasisMicrostate,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    noncomm_ring
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup (A.model n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hAvg.eigenvectorUnitary.2
  have hnormdiff : ‖Wstar - Winv‖ =
      ‖(A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ‖ := by
    rw [hdiff, KazhdanCornerMatrices.norm_unitary_conjugate hUstar]
    rw [show (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ - A.map n g⁻¹ =
      -((A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) by abel, norm_neg]
  rw [hblockStar]
  have hsplit :
      KazhdanCornerMatrices.coordinateBlock p (fun i ↦ ¬p i) Wstar =
        KazhdanCornerMatrices.coordinateBlock p (fun i ↦ ¬p i) Winv +
          KazhdanCornerMatrices.coordinateBlock p (fun i ↦ ¬p i)
            (Wstar - Winv) := by
    ext i j
    simp [KazhdanCornerMatrices.coordinateBlock, Matrix.toBlock_apply]
  rw [hsplit]
  calc
    ‖KazhdanCornerMatrices.coordinateBlock p (fun i ↦ ¬p i) Winv +
        KazhdanCornerMatrices.coordinateBlock p (fun i ↦ ¬p i)
          (Wstar - Winv)‖ ≤
      ‖KazhdanCornerMatrices.coordinateBlock p (fun i ↦ ¬p i) Winv‖ +
        ‖KazhdanCornerMatrices.coordinateBlock p (fun i ↦ ¬p i)
          (Wstar - Winv)‖ := norm_add_le _ _
    _ ≤ eta / 2 + eta / 2 := add_le_add
      (hmove n ((le_max_left _ _).trans hn))
      ((KazhdanCornerMatrices.norm_coordinateBlock_le p (fun i ↦ ¬p i)
        (Wstar - Winv)).trans (by
          rw [hnormdiff]
          exact hinv n ((le_max_right _ _).trans hn)))
    _ = eta := by ring

/-- Conjugating into the subgroup spectral basis preserves the ambient
weak-MF multiplication defect exactly. -/
theorem norm_ambientEigenbasisMicrostate_mul_defect_eq
    (A : WeakMFApproximation H) (N : Subgroup H) (D : Setup A N)
    (n : ℕ) (g h : H) :
    ‖ambientEigenbasisMicrostate A N D n (g * h) -
        ambientEigenbasisMicrostate A N D n g *
          ambientEigenbasisMicrostate A N D n h‖ =
      ‖(A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) * A.map n h‖ := by
  let hAvg := KazhdanCornerMatrices.movingHermitianAverage_isHermitian
    (restrictedApproximation A N) D.S n
  let U : Matrix (A.model n) (A.model n) ℂ := hAvg.eigenvectorUnitary
  have hU : U * Uᴴ = 1 :=
    Unitary.mul_star_self_of_mem hAvg.eigenvectorUnitary.2
  have hEq :
      ambientEigenbasisMicrostate A N D n (g * h) -
          ambientEigenbasisMicrostate A N D n g *
            ambientEigenbasisMicrostate A N D n h =
        Uᴴ * ((A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) * A.map n h) * U := by
    change Uᴴ * (A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) * U -
      (Uᴴ * (A.map n g : Matrix (A.model n) (A.model n) ℂ) * U) *
        (Uᴴ * (A.map n h : Matrix (A.model n) (A.model n) ℂ) * U) = _
    exact KazhdanCornerMatrices.unitaryConjugation_mul_defect_eq hU
  rw [hEq]
  simpa only [Matrix.conjTranspose_conjTranspose] using
    KazhdanCornerMatrices.norm_unitary_conjugate
    (show Uᴴ ∈ Matrix.unitaryGroup (A.model n) ℂ by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
      exact Unitary.star_mul_self_of_mem hAvg.eigenvectorUnitary.2)

/-- Compress an ambient microstate to the subgroup moving spectral corner. -/
noncomputable def ambientMovingCompression (A : WeakMFApproximation H)
    (N : Subgroup H) (D : Setup A N) (n : ℕ) (g : H) :
    Matrix (MovingIndex A N D n) (MovingIndex A N D n) ℂ :=
  KazhdanCornerMatrices.principalBlock
    (KazhdanCornerMatrices.movingPredicate
      (restrictedApproximation A N) D.S D.cutoff n)
    (ambientEigenbasisMicrostate A N D n g)

/-- The ambient moving compression is a contraction. -/
theorem norm_ambientMovingCompression_le_one
    (A : WeakMFApproximation H) (N : Subgroup H) (D : Setup A N)
    (n : ℕ) (g : H) : ‖ambientMovingCompression A N D n g‖ ≤ 1 := by
  classical
  letI : Nonempty (A.model n) :=
    Fintype.card_pos_iff.mp (A.modelNonempty n)
  exact (KazhdanCornerMatrices.norm_principalBlock_le
    (KazhdanCornerMatrices.movingPredicate
      (restrictedApproximation A N) D.S D.cutoff n)
    (ambientEigenbasisMicrostate A N D n g)).trans_eq
      (CStarRing.norm_of_mem_unitary
        (ambientEigenbasisMicrostate_mem_unitaryGroup A N D n g))

/-- Exact multiplication-defect estimate before proving that normality makes
the two off-diagonal blocks vanish. -/
theorem norm_ambientMovingCompression_mul_defect_le
    (A : WeakMFApproximation H) (N : Subgroup H) (D : Setup A N)
    (n : ℕ) (g h : H) :
    ‖ambientMovingCompression A N D n (g * h) -
        ambientMovingCompression A N D n g *
          ambientMovingCompression A N D n h‖ ≤
      ‖(A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) * A.map n h‖ +
      ‖KazhdanCornerMatrices.coordinateBlock
        (KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n)
        (fun i ↦ ¬KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n i)
        (ambientEigenbasisMicrostate A N D n g)‖ *
      ‖KazhdanCornerMatrices.coordinateBlock
        (fun i ↦ ¬KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n i)
        (KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n)
        (ambientEigenbasisMicrostate A N D n h)‖ := by
  classical
  have hbound := KazhdanCornerMatrices.norm_principalBlock_mul_defect_le
    (KazhdanCornerMatrices.movingPredicate
      (restrictedApproximation A N) D.S D.cutoff n)
    (ambientEigenbasisMicrostate A N D n (g * h))
    (ambientEigenbasisMicrostate A N D n g)
    (ambientEigenbasisMicrostate A N D n h)
  rw [norm_ambientEigenbasisMicrostate_mul_defect_eq A N D n g h] at hbound
  change
    ‖KazhdanCornerMatrices.principalBlock
          (KazhdanCornerMatrices.movingPredicate
            (restrictedApproximation A N) D.S D.cutoff n)
          (ambientEigenbasisMicrostate A N D n (g * h)) -
        KazhdanCornerMatrices.principalBlock
            (KazhdanCornerMatrices.movingPredicate
              (restrictedApproximation A N) D.S D.cutoff n)
            (ambientEigenbasisMicrostate A N D n g) *
          KazhdanCornerMatrices.principalBlock
            (KazhdanCornerMatrices.movingPredicate
              (restrictedApproximation A N) D.S D.cutoff n)
            (ambientEigenbasisMicrostate A N D n h)‖ ≤ _
  exact hbound

/-- Ambient moving-corner compressions are asymptotically multiplicative.
This is the finite-dimensional normal-corner statement needed before polar
correction. -/
theorem ambientMovingCompression_mul_defect_eventually_small
    (A : WeakMFApproximation H) (N : Subgroup H) [N.Normal]
    (D : Setup A N) (g h : H) (eta : ℝ) (heta : 0 < eta) :
    ∃ stage : ℕ, ∀ n ≥ stage,
      ‖ambientMovingCompression A N D n (g * h) -
        ambientMovingCompression A N D n g *
          ambientMovingCompression A N D n h‖ ≤ eta := by
  obtain ⟨Ndef, hdef⟩ := A.asymptoticallyMultiplicative g h
    (eta / 2) (by linarith)
  obtain ⟨Nblock, hblock⟩ := ambientMovingToTopBlock_vanishing A N D g
    (eta / 2) (by linarith)
  refine ⟨max Ndef Nblock, fun n hn ↦ ?_⟩
  have hother :
      ‖KazhdanCornerMatrices.coordinateBlock
        (fun i ↦ ¬KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n i)
        (KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n)
        (ambientEigenbasisMicrostate A N D n h)‖ ≤ 1 := by
    calc
      _ ≤ ‖ambientEigenbasisMicrostate A N D n h‖ :=
        KazhdanCornerMatrices.norm_coordinateBlock_le _ _ _
      _ = 1 := CStarRing.norm_of_mem_unitary
        (ambientEigenbasisMicrostate_mem_unitaryGroup A N D n h)
  calc
    ‖ambientMovingCompression A N D n (g * h) -
        ambientMovingCompression A N D n g *
          ambientMovingCompression A N D n h‖ ≤
      ‖(A.map n (g * h) : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) * A.map n h‖ +
      ‖KazhdanCornerMatrices.coordinateBlock
        (KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n)
        (fun i ↦ ¬KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n i)
        (ambientEigenbasisMicrostate A N D n g)‖ *
      ‖KazhdanCornerMatrices.coordinateBlock
        (fun i ↦ ¬KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n i)
        (KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n)
        (ambientEigenbasisMicrostate A N D n h)‖ :=
      norm_ambientMovingCompression_mul_defect_le A N D n g h
    _ ≤ eta / 2 + (eta / 2) * 1 := add_le_add
      (hdef n ((le_max_left _ _).trans hn))
      (mul_le_mul
        (hblock n ((le_max_right _ _).trans hn)) hother
        (norm_nonneg _) (by linarith))
    _ = eta := by ring

/-- Ambient moving-corner compressions are asymptotically unitary before
polar correction. -/
theorem ambientMovingCompression_gram_eventually_small
    (A : WeakMFApproximation H) (N : Subgroup H) [N.Normal]
    (D : Setup A N) (g : H) (eta : ℝ) (heta : 0 < eta) :
    ∃ stage : ℕ, ∀ n ≥ stage,
      ‖KazhdanCornerMatrices.cornerGram
          (ambientMovingCompression A N D n g) - 1‖ ≤ eta := by
  obtain ⟨stage, hstage⟩ := ambientTopToMovingBlock_vanishing A N D g
    (Real.sqrt eta) (Real.sqrt_pos.2 heta)
  refine ⟨stage, fun n hn ↦ ?_⟩
  let p := KazhdanCornerMatrices.movingPredicate
    (restrictedApproximation A N) D.S D.cutoff n
  have hunitary :
      (ambientEigenbasisMicrostate A N D n g)ᴴ *
        ambientEigenbasisMicrostate A N D n g = 1 := by
    have hmem := ambientEigenbasisMicrostate_mem_unitaryGroup A N D n g
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmem
    exact hmem
  calc
    ‖KazhdanCornerMatrices.cornerGram
        (ambientMovingCompression A N D n g) - 1‖ ≤
      ‖KazhdanCornerMatrices.coordinateBlock (fun i ↦ ¬p i) p
        (ambientEigenbasisMicrostate A N D n g)‖ ^ 2 :=
      KazhdanCornerMatrices.norm_principalBlock_gram_sub_one_le
        p (ambientEigenbasisMicrostate A N D n g) hunitary
    _ ≤ (Real.sqrt eta) ^ 2 := by
      exact sq_le_sq₀ (norm_nonneg _)
        (Real.sqrt_nonneg _) |>.2 (hstage n hn)
    _ = eta := Real.sq_sqrt heta.le

end InternalRadicalGap
end NonsoficGroupsExist
