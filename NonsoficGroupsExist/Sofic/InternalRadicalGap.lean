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

/-- Restrict one fixed sequential approximation of `H` to a subgroup.  It is
important that this uses the same matrices as the ambient approximation. -/
def restrictedApproximation (A : WeakMFApproximation H) (N : Subgroup H) :
    WeakMFApproximation N :=
  A.comap N.subtype Subtype.val_injective

@[simp] theorem restrictedApproximation_model
    (A : WeakMFApproximation H) (N : Subgroup H) (n : ℕ) :
    (restrictedApproximation A N).model n = A.model n := rfl

@[simp] theorem restrictedApproximation_map
    (A : WeakMFApproximation H) (N : Subgroup H) (n : ℕ) (x : N) :
    (restrictedApproximation A N).map n x = A.map n x := rfl

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
  hAvg.eigenvectorUnitaryᴴ *
    (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
      hAvg.eigenvectorUnitary

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

/-- On subgroup elements the ambient matrix is literally the ordinary
eigenbasis microstate of the restricted approximation. -/
theorem ambientEigenbasisMicrostate_subgroup
    (A : WeakMFApproximation H) (N : Subgroup H) (D : Setup A N)
    (n : ℕ) (x : N) :
    ambientEigenbasisMicrostate A N D n x =
      KazhdanCornerMatrices.eigenbasisMicrostate
        (restrictedApproximation A N) D.S n x := rfl

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
  exact KazhdanCornerMatrices.norm_unitary_conjugate
    (show Uᴴ ∈ Matrix.unitaryGroup (A.model n) ℂ by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
      exact Unitary.star_mul_self_of_mem hAvg.eigenvectorUnitary.2) _

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
  exact hbound

end InternalRadicalGap
end NonsoficGroupsExist
