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

end InternalRadicalGap
end NonsoficGroupsExist
