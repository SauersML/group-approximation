import GroupApproximation.Sofic.HyperlinearResidualDetector
import GroupApproximation.Sofic.KazhdanCornerDiagonal

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

namespace GroupApproximation
namespace InternalRadicalGap

open Filter Matrix
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
    change ‖Matrix.diagonal (fun i : {i // p i} ↦ (d i)⁻¹)‖ ≤ c⁻¹
    rw [Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hc.le)).2 fun i ↦ ?_
    rw [norm_inv]
    have hdi : 0 < ‖d i‖ := hc.trans_le (hd i i.property)
    exact (inv_le_inv₀ hdi hc).2 (hd i i.property)
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

/-- Restrict the given ambient weak-MF approximation to the subgroup, as an
operator-norm almost representation.  Its finite matrix carriers are
definitionally the ambient carriers.  Separation is deliberately dropped: the
compressed corner arguments below never use it. -/
abbrev restrictedApproximation (A : WeakMFApproximation H) (N : Subgroup H) :
    OpAlmostRepresentation N :=
  A.toOpAlmostRepresentation.comap N.subtype

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
  ⟨g⁻¹ * x * g,
    (inferInstance : N.Normal).conj_mem' (x : H) x.property g⟩

@[simp]
theorem normalConjugate_coe (N : Subgroup H) [N.Normal] (g : H) (x : N) :
    (normalConjugate N g x : H) = g⁻¹ * x * g :=
  rfl

/-- Normality converts subgroup top-corner invariance into approximate
invariance of an ambient translate of that corner. -/
theorem subgroup_displacement_mul_ambient_top_vanishing
    (A : WeakMFApproximation H) (N : Subgroup H) [N.Normal]
    (D : Setup A N) (g : H) (s : N) :
    KazhdanCornerMatrices.OpNormVanishing A.toOpAlmostRepresentation (fun n ↦
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
    A.toOpAlmostRepresentation (s : H) g).mul_right_of_norm_le_one P hP
  have hgx := (KazhdanCornerMatrices.multiplicativeDefect_vanishing
    A.toOpAlmostRepresentation g (x : H)).mul_right_of_norm_le_one P hP
  have hmapNorm : ∀ n,
      ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ)‖ ≤ 1 := fun n ↦ by
    letI : Nonempty (A.model n) :=
      Fintype.card_pos_iff.mp (A.modelNonempty n)
    exact (CStarRing.norm_of_mem_unitary (A.map n g).2).le
  have hx := (subgroupTopSpectralDisplacement_vanishing A N D x).mul_left_of_norm_le_one
    (fun n ↦ (A.map n g : Matrix (A.model n) (A.model n) ℂ)) hmapNorm
  change KazhdanCornerMatrices.OpNormVanishing A.toOpAlmostRepresentation (fun n ↦
    (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
      (((A.map n (x : H) : Matrix (A.model n) (A.model n) ℂ) - 1) * P n)) at hx
  have htotal := hx.add hgx |>.sub hsg
  exact htotal.congr fun n ↦ by
    have hgroup : (s : H) * g = g * (x : H) := by
      simp only [x, normalConjugate_coe]
      simp [mul_assoc]
    change
      (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          (((A.map n (x : H) : Matrix (A.model n) (A.model n) ℂ) - 1) * P n) +
        ((A.map n (g * (x : H)) : Matrix (A.model n) (A.model n) ℂ) -
          A.map n g * A.map n (x : H)) * P n -
        ((A.map n ((s : H) * g) : Matrix (A.model n) (A.model n) ℂ) -
          A.map n (s : H) * A.map n g) * P n =
      ((A.map n (s : H) : Matrix (A.model n) (A.model n) ℂ) - 1) *
        A.map n g * P n
    rw [hgroup]
    noncomm_ring

/-- The subgroup orbit average acts asymptotically as the identity on every
ambient translate of the retained top corner. -/
theorem matrixAverage_sub_one_mul_ambient_top_vanishing
    (A : WeakMFApproximation H) (N : Subgroup H) [N.Normal]
    (D : Setup A N) (g : H) :
    KazhdanCornerMatrices.OpNormVanishing A.toOpAlmostRepresentation (fun n ↦
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
  have hsum := KazhdanCornerMatrices.OpNormVanishing.finset_sum
    (A := A.toOpAlmostRepresentation) D.S X
    (fun s _ ↦ subgroup_displacement_mul_ambient_top_vanishing A N D g s)
  have hscaled := hsum.smul (((D.S.card : ℂ)⁻¹))
  have hcard : (D.S.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr ⟨1, D.one_mem⟩)
  exact hscaled.congr fun n ↦ by
    change ((D.S.card : ℂ)⁻¹) •
        (∑ s ∈ D.S,
          ((A.map n (s : H) : Matrix (A.model n) (A.model n) ℂ) - 1) *
            (A.map n g : Matrix (A.model n) (A.model n) ℂ) * P n) =
      (((D.S.card : ℂ)⁻¹) •
          (∑ s ∈ D.S,
            (A.map n (s : H) : Matrix (A.model n) (A.model n) ℂ)) - 1) *
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) * P n
    have hones : ((D.S.card : ℂ)⁻¹) •
        (∑ _s ∈ D.S, (1 : Matrix (A.model n) (A.model n) ℂ)) = 1 := by
      rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ hcard, one_smul]
    rw [show (∑ s ∈ D.S,
          ((A.map n (s : H) : Matrix (A.model n) (A.model n) ℂ) - 1) *
            (A.map n g : Matrix (A.model n) (A.model n) ℂ) * P n) =
        ((∑ s ∈ D.S,
          (A.map n (s : H) : Matrix (A.model n) (A.model n) ℂ)) -
            ∑ _s ∈ D.S, 1) *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) * P n by
      simp_rw [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
      ]
    rw [← smul_mul_assoc, ← smul_mul_assoc, smul_sub, hones]

/-- Replacing the weak-MF orbit average by its exact Hermitian part preserves
ambient top-corner invariance. -/
theorem hermitianAverage_sub_one_mul_ambient_top_vanishing
    (A : WeakMFApproximation H) (N : Subgroup H) [N.Normal]
    (D : Setup A N) (g : H) :
    KazhdanCornerMatrices.OpNormVanishing A.toOpAlmostRepresentation (fun n ↦
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
    letI : Nonempty (A.model n) :=
      Fintype.card_pos_iff.mp (A.modelNonempty n)
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
  {i : A.model n //
    KazhdanCornerMatrices.movingPredicate
      (restrictedApproximation A N) D.S D.cutoff n i}

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
  have hsub :
      KazhdanCornerMatrices.hermitianAverage
          (restrictedApproximation A N) D.S n - 1 =
        U * (L - 1) * Uᴴ := by
    rw [hHdiag]
    calc
      U * L * Uᴴ - 1 = U * L * Uᴴ - U * Uᴴ := by rw [hUUstar]
      _ = U * (L - 1) * Uᴴ := by noncomm_ring
  have hconj : Uᴴ * R * U = (L - 1) * W * Dtop := by
    change Uᴴ *
      ((KazhdanCornerMatrices.hermitianAverage
          (restrictedApproximation A N) D.S n - 1) *
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          KazhdanCornerMatrices.spectralAbove
            (KazhdanCornerMatrices.hermitianAverage
              (restrictedApproximation A N) D.S n)
            (KazhdanCornerMatrices.hermitianAverage_conjTranspose
              (restrictedApproximation A N) D.S n) D.cutoff) * U = _
    rw [hsub, hPdiag]
    calc
      Uᴴ * (U * (L - 1) * Uᴴ *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          (U * Dtop * Uᴴ)) * U =
        (Uᴴ * U) * (L - 1) *
          (Uᴴ * (A.map n g : Matrix (A.model n) (A.model n) ℂ) * U) *
          Dtop * (Uᴴ * U) := by noncomm_ring
      _ = (L - 1) * W * Dtop := by
        simp only [hUU, one_mul, mul_one]
        rfl
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
      rw [show ‖Uᴴ * R * U‖ = ‖R‖ by
        simpa only [Matrix.conjTranspose_conjTranspose] using
          KazhdanCornerMatrices.norm_unitary_conjugate hUstar (D := R)]

/-- Normality and the subgroup spectral gap make the ambient moving-to-top
off-diagonal block vanish in operator norm. -/
theorem ambientMovingToTopBlock_vanishing
    (A : WeakMFApproximation H) (N : Subgroup H) [N.Normal]
    (D : Setup A N) (g : H) :
    ∀ eta : ℝ, 0 < eta → ∃ stage, ∀ n ≥ stage,
      ‖KazhdanCornerMatrices.coordinateBlock
        (KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n)
        (fun i ↦ ¬KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n i)
        (ambientEigenbasisMicrostate A N D n g)‖ ≤ eta := by
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
    ∀ eta : ℝ, 0 < eta → ∃ stage, ∀ n ≥ stage,
      ‖KazhdanCornerMatrices.coordinateBlock
        (fun i ↦ ¬KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n i)
        (KazhdanCornerMatrices.movingPredicate
          (restrictedApproximation A N) D.S D.cutoff n)
        (ambientEigenbasisMicrostate A N D n g)‖ ≤ eta := by
  intro eta heta
  obtain ⟨Nmove, hmove⟩ := ambientMovingToTopBlock_vanishing A N D g⁻¹
    (eta / 2) (by linarith)
  obtain ⟨Ninv, hinv⟩ := KazhdanCornerMatrices.map_inv_vanishing A.toOpAlmostRepresentation g
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
    rw [hdiff]
    rw [show ‖Uᴴ * ((A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ -
        A.map n g⁻¹) * U‖ =
      ‖(A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ - A.map n g⁻¹‖ by
        simpa only [Matrix.conjTranspose_conjTranspose] using
          KazhdanCornerMatrices.norm_unitary_conjugate hUstar
            (D := (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ -
              (A.map n g⁻¹ : Matrix (A.model n) (A.model n) ℂ))]
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

/-- On subgroup elements, the ambient compression is exactly the ordinary
moving compression of the restricted weak-MF model. -/
@[simp]
theorem ambientMovingCompression_subgroup_eq
    (A : WeakMFApproximation H) (N : Subgroup H) (D : Setup A N)
    (n : ℕ) (s : N) :
    ambientMovingCompression A N D n (s : H) =
      KazhdanCornerMatrices.movingCompression
        (restrictedApproximation A N) D.S D.cutoff n s :=
  rfl

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
  letI : Nonempty (A.model n) :=
    Fintype.card_pos_iff.mp (A.modelNonempty n)
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

/-- The subgroup moving corner is eventually nonempty. -/
theorem eventually_nonempty_movingIndex
    (A : WeakMFApproximation H) (N : Subgroup H) [Nontrivial N]
    (D : Setup A N) :
    ∃ stage : ℕ, ∀ n ≥ stage, Nonempty (MovingIndex A N D n) := by
  simpa only [MovingIndex, KazhdanCornerMatrices.WeakMFMovingIndex] using
    KazhdanCornerMatrices.eventually_nonempty_weakMFMovingIndex
      D.kazhdan D.S (by rfl) D.one_mem D.epsilon_le_one D.symmetric
      D.generates (A.comap N.subtype Subtype.val_injective) D.gap_lt_cutoff

/-- A cofinal schedule on which the moving corner is nonempty and the first
`n + 1` ambient elements all have controlled Gram defect. -/
structure AmbientMovingCornerSchedule
    (A : WeakMFApproximation H) (N : Subgroup H) [Nontrivial N]
    (D : Setup A N) where
  enumerate : ℕ → H
  enumerate_surjective : Function.Surjective enumerate
  stage : ℕ → ℕ
  stage_ge : ∀ n, n ≤ stage n
  moving_nonempty : ∀ n, Nonempty (MovingIndex A N D (stage n))
  gram_close : ∀ n k, k ≤ n →
    ‖KazhdanCornerMatrices.cornerGram
        (ambientMovingCompression A N D (stage n) (enumerate k)) - 1‖ ≤
      KazhdanCornerMatrices.diagonalTolerance n

/-- Countability supplies a simultaneous ambient normal-corner schedule. -/
theorem exists_ambientMovingCornerSchedule
    [Countable H] (A : WeakMFApproximation H) (N : Subgroup H)
    [N.Normal] [Nontrivial N] (D : Setup A N) :
    Nonempty (AmbientMovingCornerSchedule A N D) := by
  classical
  obtain ⟨enumerate, henumerate⟩ := exists_surjective_nat H
  obtain ⟨Nzero, hNzero⟩ := eventually_nonempty_movingIndex A N D
  let F : ℕ → Finset H := fun n ↦ (Finset.range (n + 1)).image enumerate
  have hsimultaneous (n : ℕ) : ∃ stage, ∀ m ≥ stage, ∀ g ∈ F n,
      ‖KazhdanCornerMatrices.cornerGram
          (ambientMovingCompression A N D m g) - 1‖ ≤
        KazhdanCornerMatrices.diagonalTolerance n := by
    apply eventually_finset (F n)
    intro g _
    exact ambientMovingCompression_gram_eventually_small A N D g
      (KazhdanCornerMatrices.diagonalTolerance n)
      (KazhdanCornerMatrices.diagonalTolerance_pos n)
  let threshold : ℕ → ℕ := fun n ↦ Classical.choose (hsimultaneous n)
  have hthreshold (n : ℕ) : ∀ m ≥ threshold n, ∀ g ∈ F n,
      ‖KazhdanCornerMatrices.cornerGram
          (ambientMovingCompression A N D m g) - 1‖ ≤
        KazhdanCornerMatrices.diagonalTolerance n :=
    Classical.choose_spec (hsimultaneous n)
  let stage : ℕ → ℕ := fun n ↦ max n (max Nzero (threshold n))
  refine ⟨{
    enumerate := enumerate
    enumerate_surjective := henumerate
    stage := stage
    stage_ge := fun n ↦ le_max_left _ _
    moving_nonempty := fun n ↦ hNzero (stage n) (by
      exact (le_max_left Nzero (threshold n)).trans
        (le_max_right n (max Nzero (threshold n))))
    gram_close := ?_ }⟩
  intro n k hk
  exact hthreshold n (stage n)
    ((le_max_right Nzero (threshold n)).trans
      (le_max_right n (max Nzero (threshold n)))) (enumerate k)
    (Finset.mem_image.mpr ⟨k, by simp only [Finset.mem_range]; omega, rfl⟩)

/-- A chosen enumeration index for an ambient element. -/
noncomputable def AmbientMovingCornerSchedule.code
    {A : WeakMFApproximation H} {N : Subgroup H} [Nontrivial N]
    {D : Setup A N}
    (R : AmbientMovingCornerSchedule A N D) (g : H) : ℕ :=
  Classical.choose (R.enumerate_surjective g)

@[simp]
theorem AmbientMovingCornerSchedule.enumerate_code
    {A : WeakMFApproximation H} {N : Subgroup H} [Nontrivial N]
    {D : Setup A N}
    (R : AmbientMovingCornerSchedule A N D) (g : H) :
    R.enumerate (R.code g) = g :=
  Classical.choose_spec (R.enumerate_surjective g)

/-- The selected ambient moving-corner matrix model. -/
noncomputable abbrev AmbientMovingCornerSchedule.model
    {A : WeakMFApproximation H} {N : Subgroup H} [Nontrivial N]
    {D : Setup A N}
    (R : AmbientMovingCornerSchedule A N D) (n : ℕ) : FiniteModel :=
  KazhdanCornerMatrices.weakMFMovingModel
    (restrictedApproximation A N) D.S D.cutoff (R.stage n)

theorem AmbientMovingCornerSchedule.model_nonempty
    {A : WeakMFApproximation H} {N : Subgroup H} [Nontrivial N]
    {D : Setup A N}
    (R : AmbientMovingCornerSchedule A N D) (n : ℕ) :
    0 < Fintype.card (R.model n) := by
  rw [Fintype.card_pos_iff]
  exact R.moving_nonempty n

/-- Exact scheduled unitary obtained by polar correction once an ambient
element is active. -/
noncomputable def AmbientMovingCornerSchedule.map
    {A : WeakMFApproximation H} {N : Subgroup H} [Nontrivial N]
    {D : Setup A N}
    (R : AmbientMovingCornerSchedule A N D) (n : ℕ) (g : H) :
    Matrix.unitaryGroup (R.model n) ℂ := by
  by_cases hg : R.code g ≤ n
  · have hclose := R.gram_close n (R.code g) hg
    rw [R.enumerate_code g] at hclose
    have hclose' :
        ‖KazhdanCornerMatrices.cornerGram
            (ambientMovingCompression A N D (R.stage n) g) -
          (1 : Matrix (R.model n) (R.model n) ℂ)‖ ≤
            KazhdanCornerMatrices.diagonalTolerance n := by
      simpa only using hclose
    exact KazhdanCornerMatrices.polarCorrectUnitary
      (ambientMovingCompression A N D (R.stage n) g)
      (KazhdanCornerMatrices.cornerGram_isHermitian _)
      (KazhdanCornerMatrices.diagonalTolerance_le_half n) hclose'
  · exact 1

/-- Active scheduled unitaries remain close to their uncorrected ambient
moving compressions. -/
theorem AmbientMovingCornerSchedule.map_close_of_code_le
    {A : WeakMFApproximation H} {N : Subgroup H} [Nontrivial N]
    {D : Setup A N}
    (R : AmbientMovingCornerSchedule A N D) (n : ℕ) (g : H)
    (hg : R.code g ≤ n) :
    ‖(R.map n g : Matrix (R.model n) (R.model n) ℂ) -
        ambientMovingCompression A N D (R.stage n) g‖ ≤
      2 * KazhdanCornerMatrices.diagonalTolerance n := by
  rw [AmbientMovingCornerSchedule.map, dif_pos hg]
  exact KazhdanCornerMatrices.norm_polarCorrect_sub_le
    (ambientMovingCompression A N D (R.stage n) g)
    (KazhdanCornerMatrices.cornerGram_isHermitian _)
    (norm_ambientMovingCompression_le_one A N D (R.stage n) g)
    (KazhdanCornerMatrices.diagonalTolerance_pos n).le
    (KazhdanCornerMatrices.diagonalTolerance_le_half n)
    (by simpa only [R.enumerate_code g] using
      R.gram_close n (R.code g) hg)

/-- The scheduled exact unitaries are asymptotically multiplicative in
operator norm. -/
theorem AmbientMovingCornerSchedule.map_multiplicative_eventually_op
    {A : WeakMFApproximation H} {N : Subgroup H} [N.Normal] [Nontrivial N]
    {D : Setup A N}
    (R : AmbientMovingCornerSchedule A N D) (g h : H) :
    ∀ eta : ℝ, 0 < eta → ∃ stage, ∀ n ≥ stage,
      ‖(R.map n (g * h) : Matrix (R.model n) (R.model n) ℂ) -
        (R.map n g : Matrix (R.model n) (R.model n) ℂ) * R.map n h‖ ≤ eta := by
  intro eta heta
  obtain ⟨Nmul, hmul⟩ := ambientMovingCompression_mul_defect_eventually_small
    A N D g h (eta / 2) (by linarith)
  obtain ⟨Ntol, htol⟩ := KazhdanCornerMatrices.diagonalTolerance_eventually_le
    (show 0 < eta / 12 by linarith)
  let Ncode := max (R.code (g * h)) (max (R.code g) (R.code h))
  refine ⟨max Nmul (max Ntol Ncode), fun n hn ↦ ?_⟩
  have hnMul : Nmul ≤ R.stage n := by
    exact (by omega : Nmul ≤ n).trans (R.stage_ge n)
  have hnTol : Ntol ≤ n := by omega
  have hnCode : Ncode ≤ n := by omega
  have hghActive : R.code (g * h) ≤ n := by dsimp [Ncode] at hnCode; omega
  have hgActive : R.code g ≤ n := by dsimp [Ncode] at hnCode; omega
  have hhActive : R.code h ≤ n := by dsimp [Ncode] at hnCode; omega
  let Wgh : Matrix (R.model n) (R.model n) ℂ := R.map n (g * h)
  let Wg : Matrix (R.model n) (R.model n) ℂ := R.map n g
  let Wh : Matrix (R.model n) (R.model n) ℂ := R.map n h
  let Cgh : Matrix (R.model n) (R.model n) ℂ :=
    ambientMovingCompression A N D (R.stage n) (g * h)
  let Cg : Matrix (R.model n) (R.model n) ℂ :=
    ambientMovingCompression A N D (R.stage n) g
  let Ch : Matrix (R.model n) (R.model n) ℂ :=
    ambientMovingCompression A N D (R.stage n) h
  have hclosegh : ‖Wgh - Cgh‖ ≤
      2 * KazhdanCornerMatrices.diagonalTolerance n :=
    R.map_close_of_code_le n (g * h) hghActive
  have hcloseg : ‖Wg - Cg‖ ≤
      2 * KazhdanCornerMatrices.diagonalTolerance n :=
    R.map_close_of_code_le n g hgActive
  have hcloseh : ‖Wh - Ch‖ ≤
      2 * KazhdanCornerMatrices.diagonalTolerance n :=
    R.map_close_of_code_le n h hhActive
  have hcloseg' : ‖Cg - Wg‖ ≤
      2 * KazhdanCornerMatrices.diagonalTolerance n := by
    rw [show Cg - Wg = -(Wg - Cg) by abel, norm_neg]
    exact hcloseg
  have hcloseh' : ‖Ch - Wh‖ ≤
      2 * KazhdanCornerMatrices.diagonalTolerance n := by
    rw [show Ch - Wh = -(Wh - Ch) by abel, norm_neg]
    exact hcloseh
  have hdefect : ‖Cgh - Cg * Ch‖ ≤ eta / 2 := hmul (R.stage n) hnMul
  letI : Nonempty (R.model n) :=
    Fintype.card_pos_iff.mp (R.model_nonempty n)
  have hWh : ‖Wh‖ = 1 := CStarRing.norm_of_mem_unitary (R.map n h).2
  have hCg : ‖Cg‖ ≤ 1 :=
    norm_ambientMovingCompression_le_one A N D (R.stage n) g
  have htermg : ‖Cg - Wg‖ * ‖Wh‖ ≤
      (2 * KazhdanCornerMatrices.diagonalTolerance n) * 1 :=
    mul_le_mul hcloseg' hWh.le (norm_nonneg _)
      (mul_nonneg (by norm_num)
        (KazhdanCornerMatrices.diagonalTolerance_pos n).le)
  have htermh : ‖Cg‖ * ‖Ch - Wh‖ ≤
      1 * (2 * KazhdanCornerMatrices.diagonalTolerance n) :=
    mul_le_mul hCg hcloseh' (norm_nonneg _) (by norm_num)
  have hbase := KazhdanCornerMatrices.norm_mul_defect_of_perturbations
    Wgh Wg Wh Cgh Cg Ch
  have htolerance := htol n hnTol
  dsimp only [Wgh, Wg, Wh] at hbase ⊢
  nlinarith

/-- The ambient scheduled polar corrections form an asymptotic unitary
representation. -/
noncomputable def AmbientMovingCornerSchedule.toAsymptoticUnitaryRepresentation
    {A : WeakMFApproximation H} {N : Subgroup H} [N.Normal] [Nontrivial N]
    {D : Setup A N}
    (R : AmbientMovingCornerSchedule A N D) :
    AsymptoticUnitaryRepresentation H where
  model := R.model
  modelNonempty := R.model_nonempty
  map := R.map
  asymptoticallyMultiplicative := by
    intro g h eta heta
    obtain ⟨stage, hstage⟩ := R.map_multiplicative_eventually_op g h
      (Real.sqrt eta) (Real.sqrt_pos.2 heta)
    refine ⟨stage, fun n hn ↦ ?_⟩
    let E : Matrix (R.model n) (R.model n) ℂ :=
      (R.map n (g * h) : Matrix (R.model n) (R.model n) ℂ) -
        (R.map n g : Matrix (R.model n) (R.model n) ℂ) * R.map n h
    have hop : ‖E‖ ≤ Real.sqrt eta := hstage n hn
    calc
      hsDistSq (R.model n) (R.map n (g * h))
          ((R.map n g : Matrix (R.model n) (R.model n) ℂ) * R.map n h) ≤
        ‖E‖ ^ 2 := hsDistSq_le_sq_l2_opNorm (R.model n) _ _
      _ ≤ (Real.sqrt eta) ^ 2 := by
        nlinarith [norm_nonneg E, Real.sqrt_nonneg eta]
      _ = eta := Real.sq_sqrt heta.le

/-- The ambient homomorphism represented by scheduled polar-corrected
normal corners. -/
noncomputable def AmbientMovingCornerSchedule.hyperlinearHom
    {A : WeakMFApproximation H} {N : Subgroup H} [N.Normal] [Nontrivial N]
    {D : Setup A N}
    (R : AmbientMovingCornerSchedule A N D) {𝒰 : Ultrafilter ℕ}
    (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) :
    H →* UniversalHyperlinear 𝒰 R.model R.model_nonempty :=
  R.toAsymptoticUnitaryRepresentation.toUltraproductHom hcof

@[simp]
theorem AmbientMovingCornerSchedule.hyperlinearHom_apply
    {A : WeakMFApproximation H} {N : Subgroup H} [N.Normal] [Nontrivial N]
    {D : Setup A N}
    (R : AmbientMovingCornerSchedule A N D) {𝒰 : Ultrafilter ℕ}
    (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) (g : H) :
    R.hyperlinearHom hcof g = QuotientGroup.mk (fun n ↦ R.map n g) :=
  rfl

/-- The corrected subgroup generators retain the moving-corner trace
deficit inside the ambient schedule. -/
theorem AmbientMovingCornerSchedule.generator_trace_eventually_le
    {A : WeakMFApproximation H} {N : Subgroup H} [Nontrivial N]
    {D : Setup A N}
    (R : AmbientMovingCornerSchedule A N D) :
    ∃ stage, ∀ n ≥ stage,
      ∑ s ∈ D.S, (normTrace (R.model n) (R.map n (s : H))).re ≤
        (D.S.card : ℝ) * D.cutoff +
          (D.S.card : ℝ) *
            (2 * KazhdanCornerMatrices.diagonalTolerance n) := by
  classical
  obtain ⟨stage, hstage⟩ := eventually_finset D.S
    (fun s n ↦ R.code (s : H) ≤ n)
    (fun s _ ↦ ⟨R.code (s : H), fun n hn ↦ hn⟩)
  refine ⟨stage, fun n hn ↦ ?_⟩
  have hactive : ∀ s ∈ D.S, R.code (s : H) ≤ n := hstage n hn
  have hmodel : 0 < Fintype.card (R.model n) := R.model_nonempty n
  have hterm (s : N) (hs : s ∈ D.S) :
      (normTrace (R.model n) (R.map n (s : H))).re ≤
        (normTrace (R.model n)
          (ambientMovingCompression A N D (R.stage n) (s : H))).re +
            2 * KazhdanCornerMatrices.diagonalTolerance n := by
    have htrace := KazhdanCornerMatrices.re_normTrace_le_add_l2_opNorm
      (R.model n) hmodel (R.map n (s : H))
      (ambientMovingCompression A N D (R.stage n) (s : H))
    have hclose := R.map_close_of_code_le n (s : H) (hactive s hs)
    linarith
  have hsum := Finset.sum_le_sum fun s hs ↦ hterm s hs
  have hcorner :=
    KazhdanCornerMatrices.sum_re_normTrace_movingCompression_le
      (restrictedApproximation A N) D.S D.one_mem D.cutoff (R.stage n)
      (R.moving_nonempty n)
  simp only [ambientMovingCompression_subgroup_eq] at hsum
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith

/-- Eventually the corrected subgroup-generator trace average is uniformly
below one. -/
theorem AmbientMovingCornerSchedule.generator_trace_eventually_below_one
    {A : WeakMFApproximation H} {N : Subgroup H} [Nontrivial N]
    {D : Setup A N}
    (R : AmbientMovingCornerSchedule A N D) :
    ∃ stage, ∀ n ≥ stage,
      ∑ s ∈ D.S, (normTrace (R.model n) (R.map n (s : H))).re ≤
        (D.S.card : ℝ) * ((1 + D.cutoff) / 2) := by
  obtain ⟨Ntrace, htrace⟩ := R.generator_trace_eventually_le
  obtain ⟨Ntol, htol⟩ :=
    KazhdanCornerMatrices.diagonalTolerance_eventually_le
      (show 0 < (1 - D.cutoff) / 4 by linarith [D.cutoff_lt_one])
  refine ⟨max Ntrace Ntol, fun n hn ↦ ?_⟩
  have ht := htrace n ((le_max_left _ _).trans hn)
  have hd := htol n ((le_max_right _ _).trans hn)
  have hcard : (0 : ℝ) ≤ D.S.card := Nat.cast_nonneg _
  nlinarith

/-- The corrected subgroup generators retain a fixed total tracial
displacement. -/
theorem AmbientMovingCornerSchedule.generator_hsLengthSq_eventually_ge
    {A : WeakMFApproximation H} {N : Subgroup H} [Nontrivial N]
    {D : Setup A N}
    (R : AmbientMovingCornerSchedule A N D) :
    ∃ stage, ∀ n ≥ stage,
      (D.S.card : ℝ) * (1 - D.cutoff) ≤
        ∑ s ∈ D.S, hsLengthSq (R.model n) (R.map n (s : H)) := by
  obtain ⟨stage, hstage⟩ := R.generator_trace_eventually_below_one
  refine ⟨stage, fun n hn ↦ ?_⟩
  have htrace := hstage n hn
  simp_rw [KazhdanCornerMatrices.hsLengthSq_eq_two_sub_two_re_normTrace
    (R.model n) (R.model_nonempty n)]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum]
  nlinarith

/-- At least one subgroup generator survives under the ambient tracial
ultraproduct homomorphism. -/
theorem AmbientMovingCornerSchedule.exists_generator_hyperlinearHom_ne_one
    {A : WeakMFApproximation H} {N : Subgroup H} [N.Normal] [Nontrivial N]
    {D : Setup A N}
    (R : AmbientMovingCornerSchedule A N D) {𝒰 : Ultrafilter ℕ}
    (hcof : (𝒰 : Filter ℕ) ≤ Filter.cofinite) :
    ∃ s ∈ D.S, R.hyperlinearHom hcof (s : H) ≠ 1 := by
  classical
  by_contra htrivial
  push Not at htrivial
  have hnull (s : N) (hs : s ∈ D.S) :
      IsNullUnitarySeq 𝒰 R.model (fun n ↦ R.map n (s : H)) := by
    have heq : (1 : UniversalHyperlinear 𝒰 R.model R.model_nonempty) =
        QuotientGroup.mk (fun n ↦ R.map n (s : H)) := by
      rw [← R.hyperlinearHom_apply hcof (s : H)]
      exact (htrivial s hs).symm
    change QuotientGroup.mk
      (1 : ∀ n, Matrix.unitaryGroup (R.model n) ℂ) =
        QuotientGroup.mk (fun n ↦ R.map n (s : H)) at heq
    have hmem := QuotientGroup.eq.mp heq
    have hmem' : (fun n ↦ R.map n (s : H)) ∈
        nullUnitarySubgroup 𝒰 R.model R.model_nonempty := by
      simpa only [inv_one, one_mul] using hmem
    exact hmem'
  let eta : ℝ := (1 - D.cutoff) / 2
  have heta : 0 < eta := by dsimp [eta]; linarith [D.cutoff_lt_one]
  have hallSmall : ∀ᶠ n in (𝒰 : Filter ℕ), ∀ s ∈ D.S,
      hsLengthSq (R.model n) (R.map n (s : H)) < eta := by
    rw [Finset.eventually_all]
    intro s hs
    exact hnull s hs eta heta
  have hsumSmall : ∀ᶠ n in (𝒰 : Filter ℕ),
      ∑ s ∈ D.S, hsLengthSq (R.model n) (R.map n (s : H)) <
        (D.S.card : ℝ) * (1 - D.cutoff) / 2 := by
    filter_upwards [hallSmall] with n hn
    calc
      ∑ s ∈ D.S, hsLengthSq (R.model n) (R.map n (s : H)) <
          ∑ _s ∈ D.S, eta :=
        Finset.sum_lt_sum_of_nonempty ⟨1, D.one_mem⟩ hn
      _ = (D.S.card : ℝ) * (1 - D.cutoff) / 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        dsimp [eta]
        ring
  obtain ⟨stage, hstage⟩ := R.generator_hsLengthSq_eventually_ge
  have hsumLarge : ∀ᶠ n in (𝒰 : Filter ℕ),
      (D.S.card : ℝ) * (1 - D.cutoff) ≤
        ∑ s ∈ D.S, hsLengthSq (R.model n) (R.map n (s : H)) :=
    eventually_of_atTop hcof stage hstage
  obtain ⟨n, hnLarge, hnSmall⟩ := (hsumLarge.and hsumSmall).exists
  have hcard : (0 : ℝ) < D.S.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, D.one_mem⟩
  nlinarith [D.cutoff_lt_one]

/-- **Internal-radical gap bridge.**  If a countable weak-MF group contains
a nontrivial normal property-`(T)` subgroup inside its sofic residual, then
there exists a hyperlinear nonsofic group.

The witness is the range of the ambient normal-corner homomorphism into a
tracial matrix ultraproduct.  No faithfulness or trace-selection hypothesis
is required. -/
theorem exists_hyperlinear_nonsofic_of_normal_kazhdan_soficResidual
    [Countable H] (hMF : IsWeakMF H) (N : Subgroup H) [N.Normal]
    [Nontrivial N] (hT : HasKazhdanPropertyT.{0, 0} N)
    (hresidual : N ≤ soficResidual H) :
    ∃ (Q : Type) (_ : Group Q), IsHyperlinear Q ∧ ¬IsSofic Q := by
  classical
  obtain ⟨separation, hseparation, happroximation⟩ := hMF
  let A : WeakMFApproximation H :=
    Classical.choice
      (exists_weakMFApproximation hseparation happroximation)
  obtain ⟨D⟩ := exists_setup A N hT
  obtain ⟨R⟩ := exists_ambientMovingCornerSchedule A N D
  let 𝒰 : Ultrafilter ℕ := Ultrafilter.of Filter.cofinite
  have hcof : ((𝒰 : Ultrafilter ℕ) : Filter ℕ) ≤ Filter.cofinite :=
    Ultrafilter.of_le Filter.cofinite
  let rho := R.hyperlinearHom hcof
  obtain ⟨s, hsS, hsDetect⟩ :=
    R.exists_generator_hyperlinearHom_ne_one hcof
  have hsResidual : (s : H) ∈ soficResidual H := hresidual s.property
  have hrange : IsHyperlinear rho.range :=
    isHyperlinear_of_hyperlinearUltraproductEmbedding
      𝒰 R.model R.model_nonempty rho.range.subtype Subtype.val_injective
  have hnsofic : ¬IsSofic rho.range :=
    not_isSofic_range_of_soficInvisible hsResidual rho hsDetect
  exact ⟨rho.range, inferInstance, hrange, hnsofic⟩

end InternalRadicalGap
end GroupApproximation
