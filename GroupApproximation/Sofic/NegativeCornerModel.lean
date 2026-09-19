import GroupApproximation.Sofic.ApproxInvolutionCorner
import GroupApproximation.Sofic.KazhdanCornerModel
import GroupApproximation.Sofic.KazhdanCornerPolar

/-!
# The negative corner of an approximate central involution

Step 5 of the marked-compression blueprint
(`notes/NON_MF_FORMALIZATION_BLUEPRINT.md`): given a weak-MF approximation of
a group carrying a central involution `z ≠ 1`, cut every microstate by the
negative spectral sector of the rounded involution and repackage the corner
as an honest operator-norm almost representation on which `z` converges to
`-1`.

The corner coordinates are the eigenvectors of the Hermitian part of the
`z`-microstate with nonpositive eigenvalue.  In that eigenbasis the rounded
involution of `ApproxInvolutionCorner` is exactly the `±1` sign diagonal,
and the corner leakage of every group element is controlled with no
spectral gap: the `(≤0, >0)` block of the commutator `[D, V]` with the sign
diagonal `D` is exactly `-2` times the same block of `V`, so asymptotic
commutation (centrality of `z`) forces the off-corner blocks to vanish.
Principal compression then has vanishing multiplicative and Gram defects
(`norm_principalBlock_mul_defect_le`, `norm_principalBlock_gram_sub_one_le`),
polar correction makes the corner exactly unitary, and separation of `z`
from `1` keeps the corner nonempty along a tail
(`negativeProjection_eventually_ne_zero`).

Main result: `exists_negativeCorner_opAlmostRepresentation`.  This is the
finite-stage form of the central-corner cut in the non-MF manuscript
(`non_mf_groups_exist.tex`, Lemma `lem:corner`); no lower bound on the
corner ranks is consumed anywhere.  The downstream Kazhdan compressor takes
exactly the exported interface.

Mathematical provenance: compression of an approximate central involution to
its negative eigenspace appears in Slofstra--Vidick, *Entanglement in
non-local games and the hyperlinear profile of groups*, Proposition 2.7
(arXiv:1711.10676).  Their normalized Hilbert--Schmidt argument obtains a
positive relative dimension.  The operator-norm construction here needs only
that the corner is nonempty and then treats it as the whole finite model, so
no rank-density estimate is used. Bachner--Dogon--Lubotzky,
*On L1-approximation of groups*, Lemma 2.3 and Propositions 1.5 and 2.4,
already carry out the corresponding operator-norm, dimension-changing
corner restriction and polar correction for a central involution. The new
downstream ingredient here is not this local corner technology but its use in
the Kazhdan-adjoint/stable-finiteness universal-kernel argument. This file is
an independent Lean proof; no external Lean code was copied.
-/

namespace GroupApproximation
namespace NegativeCornerModel

open Matrix
open scoped Matrix.Norms.L2Operator
open ApproxInvolutionCorner
open KazhdanCornerMatrices

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-! ## The sign eigenbasis of an approximate involution -/

/-- The nonpositive spectral coordinates of the Hermitian part: the corner
predicate.  The zero eigenvalue belongs to the corner, matching the strict
threshold of `positiveProjection`. -/
def negPredicate (U : Matrix Y Y ℂ) : Y → Prop :=
  fun i => (hermitianPart_isHermitian U).eigenvalues i ≤ 0

noncomputable instance (U : Matrix Y Y ℂ) : DecidablePred (negPredicate U) :=
  fun _ => Classical.dec _

/-- The eigenvector unitary of the Hermitian part, as a matrix. -/
noncomputable def signBasis (U : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  (hermitianPart_isHermitian U).eigenvectorUnitary

theorem signBasis_star_mul_self (U : Matrix Y Y ℂ) :
    (signBasis U)ᴴ * signBasis U = 1 :=
  Unitary.star_mul_self_of_mem
    (hermitianPart_isHermitian U).eigenvectorUnitary.2

theorem signBasis_mul_star_self (U : Matrix Y Y ℂ) :
    signBasis U * (signBasis U)ᴴ = 1 :=
  Unitary.mul_star_self_of_mem
    (hermitianPart_isHermitian U).eigenvectorUnitary.2

theorem signBasis_mem_unitaryGroup (U : Matrix Y Y ℂ) :
    signBasis U ∈ Matrix.unitaryGroup Y ℂ :=
  (hermitianPart_isHermitian U).eigenvectorUnitary.2

theorem signBasis_star_mem_unitaryGroup (U : Matrix Y Y ℂ) :
    (signBasis U)ᴴ ∈ Matrix.unitaryGroup Y ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  exact signBasis_star_mul_self U

/-- Conjugation into the sign eigenbasis. -/
noncomputable def toSignBasis (U M : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  (signBasis U)ᴴ * M * signBasis U

/-- Conjugation into the eigenbasis is isometric for the operator norm. -/
theorem norm_toSignBasis (U M : Matrix Y Y ℂ) :
    ‖toSignBasis U M‖ = ‖M‖ := by
  rw [toSignBasis, CStarRing.norm_mul_mem_unitary _
      (signBasis_mem_unitaryGroup U),
    CStarRing.norm_mem_unitary_mul _ (signBasis_star_mem_unitaryGroup U)]

/-- Conjugation into the eigenbasis is additive in the middle factor. -/
theorem toSignBasis_sub (U M N : Matrix Y Y ℂ) :
    toSignBasis U (M - N) = toSignBasis U M - toSignBasis U N := by
  rw [toSignBasis, toSignBasis, toSignBasis, Matrix.mul_sub, Matrix.sub_mul]

/-- Conjugation into the eigenbasis is multiplicative. -/
theorem toSignBasis_mul (U M N : Matrix Y Y ℂ) :
    toSignBasis U (M * N) = toSignBasis U M * toSignBasis U N := by
  rw [toSignBasis, toSignBasis, toSignBasis]
  rw [show (signBasis U)ᴴ * M * signBasis U *
      ((signBasis U)ᴴ * N * signBasis U) =
      (signBasis U)ᴴ * M * (signBasis U * (signBasis U)ᴴ) *
        N * signBasis U by noncomm_ring]
  rw [signBasis_mul_star_self]
  noncomm_ring

/-- The conjugated microstate of a unitary is unitary. -/
theorem toSignBasis_mem_unitaryGroup (U : Matrix Y Y ℂ)
    {M : Matrix Y Y ℂ} (hM : M ∈ Matrix.unitaryGroup Y ℂ) :
    toSignBasis U M ∈ Matrix.unitaryGroup Y ℂ := by
  rw [toSignBasis, mul_assoc]
  exact mul_mem (signBasis_star_mem_unitaryGroup U)
    (mul_mem hM (signBasis_mem_unitaryGroup U))

/-- The `±1` sign diagonal of the rounded involution: `+1` on the strictly
positive sector and `-1` on the corner. -/
noncomputable def signDiagonal (U : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  Matrix.diagonal fun i =>
    if 0 < (hermitianPart_isHermitian U).eigenvalues i then (1 : ℂ) else -1

/-- In its own eigenbasis, the rounded involution is exactly the sign
diagonal. -/
theorem toSignBasis_roundedInvolution (U : Matrix Y Y ℂ) :
    toSignBasis U (roundedInvolution U) = signDiagonal U := by
  set P : Matrix Y Y ℂ :=
    Matrix.diagonal fun i =>
      if 0 < (hermitianPart_isHermitian U).eigenvalues i
      then (1 : ℂ) else 0 with hP
  have hPdef : positiveProjection U = signBasis U * P * (signBasis U)ᴴ := rfl
  have h1 : toSignBasis U (roundedInvolution U) =
      (2 : ℂ) • ((signBasis U)ᴴ * (signBasis U * P * (signBasis U)ᴴ) *
        signBasis U) - (signBasis U)ᴴ * signBasis U := by
    rw [toSignBasis, roundedInvolution, hPdef, Matrix.mul_sub,
      Matrix.mul_one, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have h2 : (signBasis U)ᴴ * (signBasis U * P * (signBasis U)ᴴ) *
      signBasis U = P := by
    rw [show (signBasis U)ᴴ * (signBasis U * P * (signBasis U)ᴴ) *
        signBasis U =
        ((signBasis U)ᴴ * signBasis U) * P *
          ((signBasis U)ᴴ * signBasis U) by noncomm_ring]
    rw [signBasis_star_mul_self, Matrix.one_mul, Matrix.mul_one]
  rw [h1, h2, signBasis_star_mul_self, signDiagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hi : 0 < (hermitianPart_isHermitian U).eigenvalues i
    · simp [hP, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, hi]
      norm_num
    · simp [hP, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, hi]
  · simp [hP, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

/-- The corner block of the sign diagonal is exactly `-1`. -/
theorem principalBlock_signDiagonal (U : Matrix Y Y ℂ) :
    principalBlock (negPredicate U) (signDiagonal U) = -1 := by
  ext i j
  by_cases hij : (i : Y) = (j : Y)
  · have hIJ : i = j := Subtype.ext hij
    subst hIJ
    have hi : ¬ 0 < (hermitianPart_isHermitian U).eigenvalues (i : Y) :=
      not_lt.mpr i.2
    simp [principalBlock, coordinateBlock, Matrix.toBlock_apply,
      signDiagonal, Matrix.diagonal_apply_eq, Matrix.neg_apply,
      Matrix.one_apply_eq, hi]
  · have hIJ : i ≠ j := fun h => hij (congrArg Subtype.val h)
    simp [principalBlock, coordinateBlock, Matrix.toBlock_apply,
      signDiagonal, Matrix.diagonal_apply_ne _ hij, Matrix.neg_apply,
      Matrix.one_apply_ne hIJ]

/-! ## Corner leakage from the sign commutator, with no spectral gap -/

/-- The `(corner, complement)` block of the sign commutator is exactly `-2`
times the same block of the matrix. -/
theorem coordinateBlock_sign_commutator (U M : Matrix Y Y ℂ) :
    coordinateBlock (negPredicate U) (fun i => ¬ negPredicate U i)
        (signDiagonal U * M - M * signDiagonal U) =
      (-2 : ℂ) • coordinateBlock (negPredicate U)
        (fun i => ¬ negPredicate U i) M := by
  ext i j
  have hi : ¬ 0 < (hermitianPart_isHermitian U).eigenvalues (i : Y) :=
    not_lt.mpr i.2
  have hj : 0 < (hermitianPart_isHermitian U).eigenvalues (j : Y) :=
    not_le.mp j.2
  simp only [coordinateBlock, Matrix.toBlock_apply, Matrix.sub_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, signDiagonal,
    Matrix.smul_apply, smul_eq_mul, if_neg hi, if_pos hj]
  ring

/-- The `(complement, corner)` block of the sign commutator is exactly `2`
times the same block of the matrix. -/
theorem coordinateBlock_sign_commutator' (U M : Matrix Y Y ℂ) :
    coordinateBlock (fun i => ¬ negPredicate U i) (negPredicate U)
        (signDiagonal U * M - M * signDiagonal U) =
      (2 : ℂ) • coordinateBlock (fun i => ¬ negPredicate U i)
        (negPredicate U) M := by
  ext i j
  have hi : 0 < (hermitianPart_isHermitian U).eigenvalues (i : Y) :=
    not_le.mp i.2
  have hj : ¬ 0 < (hermitianPart_isHermitian U).eigenvalues (j : Y) :=
    not_lt.mpr j.2
  simp only [coordinateBlock, Matrix.toBlock_apply, Matrix.sub_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, signDiagonal,
    Matrix.smul_apply, smul_eq_mul, if_pos hi, if_neg hj]
  ring

/-- Corner leakage bound: the off-corner block is at most half the sign
commutator. -/
theorem norm_negBlock_le_half_commutator (U M : Matrix Y Y ℂ) :
    ‖coordinateBlock (negPredicate U) (fun i => ¬ negPredicate U i) M‖ ≤
      ‖signDiagonal U * M - M * signDiagonal U‖ / 2 := by
  have hb := norm_coordinateBlock_le (negPredicate U)
    (fun i => ¬ negPredicate U i)
    (signDiagonal U * M - M * signDiagonal U)
  rw [coordinateBlock_sign_commutator, norm_smul] at hb
  have hnorm2 : ‖(-2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2] at hb
  linarith

/-- Corner leakage bound for the mirrored block. -/
theorem norm_posBlock_le_half_commutator (U M : Matrix Y Y ℂ) :
    ‖coordinateBlock (fun i => ¬ negPredicate U i) (negPredicate U) M‖ ≤
      ‖signDiagonal U * M - M * signDiagonal U‖ / 2 := by
  have hb := norm_coordinateBlock_le (fun i => ¬ negPredicate U i)
    (negPredicate U) (signDiagonal U * M - M * signDiagonal U)
  rw [coordinateBlock_sign_commutator', norm_smul] at hb
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2] at hb
  linarith

/-- A nonzero negative projection yields a corner coordinate. -/
theorem nonempty_negPredicate_of_negativeProjection_ne_zero
    (U : Matrix Y Y ℂ) (h : negativeProjection U ≠ 0) :
    Nonempty {i : Y // negPredicate U i} := by
  by_contra hempty
  have hall : ∀ i : Y,
      0 < (hermitianPart_isHermitian U).eigenvalues i := by
    intro i
    by_contra hi
    exact hempty ⟨⟨i, not_lt.mp hi⟩⟩
  have hP : positiveProjection U = 1 :=
    spectralAbove_eq_one_of_forall_lt _ _ _ hall
  exact h (by rw [negativeProjection, hP, sub_self])

/-! ## The corner microstates of an almost representation -/

variable {G : Type*} [Group G]

/-- Microstate of `g`, conjugated into the sign eigenbasis of the
`z`-microstate. -/
noncomputable def signMicrostate (A : OpAlmostRepresentation G) (z : G)
    (n : ℕ) (g : G) : Matrix (A.model n) (A.model n) ℂ :=
  toSignBasis (A.map n z : Matrix (A.model n) (A.model n) ℂ)
    (A.map n g : Matrix (A.model n) (A.model n) ℂ)

theorem signMicrostate_mem_unitaryGroup (A : OpAlmostRepresentation G)
    (z : G) (n : ℕ) (g : G) :
    signMicrostate A z n g ∈ Matrix.unitaryGroup (A.model n) ℂ :=
  toSignBasis_mem_unitaryGroup _ (A.map n g).2

/-- Corner compression of the `g`-microstate. -/
noncomputable def cornerMicrostate (A : OpAlmostRepresentation G) (z : G)
    (n : ℕ) (g : G) :
    Matrix
      {i : A.model n //
        negPredicate (A.map n z : Matrix (A.model n) (A.model n) ℂ) i}
      {i : A.model n //
        negPredicate (A.map n z : Matrix (A.model n) (A.model n) ℂ) i} ℂ :=
  principalBlock
    (negPredicate (A.map n z : Matrix (A.model n) (A.model n) ℂ))
    (signMicrostate A z n g)

/-- Corner compressions are contractions. -/
theorem norm_cornerMicrostate_le_one (A : OpAlmostRepresentation G)
    (z : G) (n : ℕ) (g : G) :
    ‖cornerMicrostate A z n g‖ ≤ 1 := by
  letI : Nonempty (A.model n) := Fintype.card_pos_iff.mp (A.modelNonempty n)
  refine (norm_principalBlock_le _ _).trans_eq ?_
  simp only [signMicrostate]
  rw [norm_toSignBasis]
  exact CStarRing.norm_of_mem_unitary (A.map n g).2

/-- The sign commutator of every fixed centralizing element vanishes. -/
theorem sign_commutator_vanishing (A : OpAlmostRepresentation G)
    {z : G} (hz : z * z = 1) {g : G} (hcomm : z * g = g * z) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖signDiagonal (A.map n z : Matrix (A.model n) (A.model n) ℂ) *
          signMicrostate A z n g -
        signMicrostate A z n g *
          signDiagonal (A.map n z : Matrix (A.model n) (A.model n) ℂ)‖
        ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := roundedInvolution_commute_map_vanishing A hz hcomm ε hε
  refine ⟨N, fun n hn => ?_⟩
  set U : Matrix (A.model n) (A.model n) ℂ :=
    (A.map n z : Matrix (A.model n) (A.model n) ℂ)
  have hcollapse :
      signDiagonal U * signMicrostate A z n g -
        signMicrostate A z n g * signDiagonal U =
      toSignBasis U (roundedInvolution U *
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) -
        (A.map n g : Matrix (A.model n) (A.model n) ℂ) *
          roundedInvolution U) := by
    rw [show signDiagonal U = toSignBasis U (roundedInvolution U) from
      (toSignBasis_roundedInvolution U).symm]
    rw [toSignBasis_sub, toSignBasis_mul, toSignBasis_mul]
    rfl
  rw [hcollapse, norm_toSignBasis]
  exact hN n hn

/-- Multiplicative defect of the corner compression vanishes for every fixed
pair of group elements. -/
theorem cornerMicrostate_multiplicative_eventually
    (A : OpAlmostRepresentation G) {z : G} (hz : z * z = 1)
    (hcentral : ∀ g : G, z * g = g * z) (g h : G) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖cornerMicrostate A z n (g * h) -
        cornerMicrostate A z n g * cornerMicrostate A z n h‖ ≤ ε := by
  intro ε hε
  obtain ⟨Nm, hNm⟩ := A.asymptoticallyMultiplicative g h (ε / 2)
    (by linarith)
  obtain ⟨Nc, hNc⟩ := sign_commutator_vanishing A hz (hcentral g) ε hε
  refine ⟨max Nm Nc, fun n hn => ?_⟩
  letI : Nonempty (A.model n) := Fintype.card_pos_iff.mp (A.modelNonempty n)
  set U : Matrix (A.model n) (A.model n) ℂ :=
    (A.map n z : Matrix (A.model n) (A.model n) ℂ)
  have hmul : ‖signMicrostate A z n (g * h) -
      signMicrostate A z n g * signMicrostate A z n h‖ ≤ ε / 2 := by
    simp only [signMicrostate]
    rw [← toSignBasis_mul, ← toSignBasis_sub, norm_toSignBasis]
    exact hNm n ((le_max_left _ _).trans hn)
  have hcrossg : ‖coordinateBlock (negPredicate U)
      (fun i => ¬ negPredicate U i) (signMicrostate A z n g)‖ ≤ ε / 2 := by
    refine (norm_negBlock_le_half_commutator U _).trans ?_
    have hc := hNc n ((le_max_right _ _).trans hn)
    linarith
  have hcrossh : ‖coordinateBlock (fun i => ¬ negPredicate U i)
      (negPredicate U) (signMicrostate A z n h)‖ ≤ 1 := by
    refine (norm_coordinateBlock_le _ _ _).trans ?_
    have hh : ‖signMicrostate A z n h‖ = 1 := by
      simp only [signMicrostate]
      rw [norm_toSignBasis]
      exact CStarRing.norm_of_mem_unitary (A.map n h).2
    exact le_of_eq hh
  calc
    ‖cornerMicrostate A z n (g * h) -
        cornerMicrostate A z n g * cornerMicrostate A z n h‖ ≤
        ‖signMicrostate A z n (g * h) -
          signMicrostate A z n g * signMicrostate A z n h‖ +
        ‖coordinateBlock (negPredicate U) (fun i => ¬ negPredicate U i)
          (signMicrostate A z n g)‖ *
        ‖coordinateBlock (fun i => ¬ negPredicate U i) (negPredicate U)
          (signMicrostate A z n h)‖ :=
      norm_principalBlock_mul_defect_le _ _ _ _
    _ ≤ ε / 2 + (ε / 2) * 1 := add_le_add hmul
        (mul_le_mul hcrossg hcrossh (norm_nonneg _) (by linarith))
    _ = ε := by ring

/-- Gram defect of the corner compression vanishes for every fixed group
element. -/
theorem cornerMicrostate_gram_eventually (A : OpAlmostRepresentation G)
    {z : G} (hz : z * z = 1) (hcentral : ∀ g : G, z * g = g * z) (g : G) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖cornerGram (cornerMicrostate A z n g) - 1‖ ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := sign_commutator_vanishing A hz (hcentral g)
    (Real.sqrt ε) (Real.sqrt_pos.2 hε)
  refine ⟨N, fun n hn => ?_⟩
  set U : Matrix (A.model n) (A.model n) ℂ :=
    (A.map n z : Matrix (A.model n) (A.model n) ℂ)
  have hunit : (signMicrostate A z n g)ᴴ * signMicrostate A z n g = 1 := by
    have hmem := signMicrostate_mem_unitaryGroup A z n g
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hmem
    exact hmem
  have hgram := norm_principalBlock_gram_sub_one_le (negPredicate U)
    (signMicrostate A z n g) hunit
  have hblock : ‖coordinateBlock (fun i => ¬ negPredicate U i)
      (negPredicate U) (signMicrostate A z n g)‖ ≤ Real.sqrt ε := by
    refine (norm_posBlock_le_half_commutator U _).trans ?_
    have hc := hN n hn
    change ‖signDiagonal U * signMicrostate A z n g -
      signMicrostate A z n g * signDiagonal U‖ ≤ Real.sqrt ε at hc
    linarith [Real.sqrt_nonneg ε]
  refine hgram.trans ?_
  have hnonneg : (0 : ℝ) ≤ ‖coordinateBlock (fun i => ¬ negPredicate U i)
      (negPredicate U) (signMicrostate A z n g)‖ := norm_nonneg _
  nlinarith [Real.sq_sqrt hε.le]

/-- The corner value of the involution converges to `-1`. -/
theorem cornerMicrostate_involution_eventually
    (A : OpAlmostRepresentation G) {z : G} (hz : z * z = 1) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖cornerMicrostate A z n z + 1‖ ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := roundedInvolution_sub_map_vanishing A hz ε hε
  refine ⟨N, fun n hn => ?_⟩
  set U : Matrix (A.model n) (A.model n) ℂ :=
    (A.map n z : Matrix (A.model n) (A.model n) ℂ)
  have hplus : cornerMicrostate A z n z + 1 =
      principalBlock (negPredicate U)
        (signMicrostate A z n z - signDiagonal U) := by
    show principalBlock (negPredicate U) (signMicrostate A z n z) + 1 = _
    rw [principalBlock_sub, principalBlock_signDiagonal]
    abel
  rw [hplus]
  refine (norm_principalBlock_le _ _).trans ?_
  have hdiff : signMicrostate A z n z - signDiagonal U =
      toSignBasis U (U - roundedInvolution U) := by
    rw [toSignBasis_sub,
      show toSignBasis U (roundedInvolution U) = signDiagonal U from
        toSignBasis_roundedInvolution U]
    rfl
  rw [hdiff, norm_toSignBasis]
  have hround := hN n hn
  rw [show U - roundedInvolution U = -(roundedInvolution U - U) by abel,
    norm_neg]
  exact hround

/-! ## The packaged corner almost representation -/

/-- The corner unitary: polar correction of the corner compression when the
Gram defect certifies invertibility, and the identity otherwise. -/
noncomputable def cornerUnitary (A : OpAlmostRepresentation G) (z : G)
    (n : ℕ) (g : G) :
    Matrix.unitaryGroup
      {i : A.model n //
        negPredicate (A.map n z : Matrix (A.model n) (A.model n) ℂ) i} ℂ :=
  if hclose : ‖cornerGram (cornerMicrostate A z n g) - 1‖ ≤ 1 / 2 then
    polarCorrectUnitary (cornerMicrostate A z n g)
      (cornerGram_isHermitian _) le_rfl hclose
  else 1

/-- On the certified branch the corner unitary is within twice the Gram
defect bound of the compression. -/
theorem norm_cornerUnitary_sub_cornerMicrostate
    (A : OpAlmostRepresentation G) (z : G) (n : ℕ) (g : G) {delta : ℝ}
    (hdelta : 0 ≤ delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hclose : ‖cornerGram (cornerMicrostate A z n g) - 1‖ ≤ delta) :
    ‖(cornerUnitary A z n g :
        Matrix
          {i : A.model n //
            negPredicate
              (A.map n z : Matrix (A.model n) (A.model n) ℂ) i}
          {i : A.model n //
            negPredicate
              (A.map n z : Matrix (A.model n) (A.model n) ℂ) i} ℂ) -
      cornerMicrostate A z n g‖ ≤ 2 * delta := by
  have hhalf : ‖cornerGram (cornerMicrostate A z n g) - 1‖ ≤ 1 / 2 :=
    hclose.trans hdeltaHalf
  simp only [cornerUnitary]
  rw [dif_pos hhalf]
  exact norm_polarCorrect_sub_le (cornerMicrostate A z n g)
    (cornerGram_isHermitian _) (norm_cornerMicrostate_le_one A z n g)
    hdelta hdeltaHalf hclose

/-- Generic triangle assembly for the corner involution estimate: if a
matrix is close to a compression whose distance to `-1` is small, its own
distance to `-1` is controlled.  Stated over an arbitrary coordinate type so
the packaging theorem applies it without re-elaborating its large corner
types. -/
theorem norm_add_one_le_of_close {Y : Type*} [Fintype Y] [DecidableEq Y]
    (C P : Matrix Y Y ℂ) {ε : ℝ}
    (h1 : ‖P - C‖ ≤ ε / 2) (h2 : ‖C + 1‖ ≤ ε / 2) :
    ‖P + 1‖ ≤ ε := by
  have hsplit : P + 1 = (P - C) + (C + 1) := by abel
  calc ‖P + 1‖ = ‖(P - C) + (C + 1)‖ := by rw [hsplit]
    _ ≤ ‖P - C‖ + ‖C + 1‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
    _ = ε := by linarith

/-- Eventual nonemptiness of the corner, from separation of the central
involution. -/
theorem nonempty_corner_eventually_of_separated
    (A : OpAlmostRepresentation G) {z : G}
    (hz : z * z = 1) {delta : ℝ} (hdelta : 0 < delta)
    (hsep : ∃ N, ∀ n ≥ N,
      delta ≤ ‖(A.map n z : Matrix (A.model n) (A.model n) ℂ) - A.map n 1‖) :
    ∃ N, ∀ n ≥ N,
      Nonempty
        {i : A.model n //
          negPredicate (A.map n z : Matrix (A.model n) (A.model n) ℂ) i} := by
  obtain ⟨N, hN⟩ := negativeProjection_eventually_ne_zero_of_separated
    A hz hdelta hsep
  exact ⟨N, fun n hn =>
    nonempty_negPredicate_of_negativeProjection_ne_zero _ (hN n hn)⟩

/-- A unitary matrix is a contraction; no nonemptiness hypothesis on the
coordinate type is needed. -/
theorem norm_le_one_of_mem_unitaryGroup {Y : Type*} [Fintype Y]
    [DecidableEq Y] {U : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) : ‖U‖ ≤ 1 := by
  rcases isEmpty_or_nonempty Y with hY | hY
  · have hzero : U = 0 := funext fun i => (hY.false i).elim
    rw [hzero, norm_zero]
    exact zero_le_one
  · exact le_of_eq (CStarRing.norm_of_mem_unitary hU)

/-- Generic triangle assembly for the corner multiplicativity estimate,
stated over an arbitrary coordinate type so that the packaged corner model
applies it without re-elaborating its large corner types. -/
theorem norm_mul_defect_le_of_close {Y : Type*} [Fintype Y] [DecidableEq Y]
    (Cg Ch Cgh Pg Ph Pgh : Matrix Y Y ℂ) {ε : ℝ}
    (hgh : ‖Pgh - Cgh‖ ≤ ε / 4) (hm : ‖Cgh - Cg * Ch‖ ≤ ε / 4)
    (hg : ‖Pg - Cg‖ ≤ ε / 4) (hh : ‖Ph - Ch‖ ≤ ε / 4)
    (hPh : ‖Ph‖ ≤ 1) (hCg : ‖Cg‖ ≤ 1) :
    ‖Pgh - Pg * Ph‖ ≤ ε := by
  have hε4 : (0 : ℝ) ≤ ε / 4 := le_trans (norm_nonneg _) hgh
  have hsplit : Pgh - Pg * Ph =
      (Pgh - Cgh) + ((Cgh - Cg * Ch) +
        ((Cg - Pg) * Ph + Cg * (Ch - Ph))) := by
    have hexpand : (Cg - Pg) * Ph + Cg * (Ch - Ph) =
        Cg * Ch - Pg * Ph := by noncomm_ring
    rw [hexpand]
    abel
  have hcross1 : ‖(Cg - Pg) * Ph‖ ≤ ε / 4 := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    calc ‖Cg - Pg‖ * ‖Ph‖ ≤ (ε / 4) * 1 := by
          refine mul_le_mul ?_ hPh (norm_nonneg _) hε4
          rw [norm_sub_rev]
          exact hg
      _ = ε / 4 := mul_one _
  have hcross2 : ‖Cg * (Ch - Ph)‖ ≤ ε / 4 := by
    refine (Matrix.l2_opNorm_mul _ _).trans ?_
    calc ‖Cg‖ * ‖Ch - Ph‖ ≤ 1 * (ε / 4) := by
          refine mul_le_mul hCg ?_ (norm_nonneg _) zero_le_one
          rw [norm_sub_rev]
          exact hh
      _ = ε / 4 := one_mul _
  calc ‖Pgh - Pg * Ph‖
      = ‖(Pgh - Cgh) + ((Cgh - Cg * Ch) +
          ((Cg - Pg) * Ph + Cg * (Ch - Ph)))‖ := by rw [hsplit]
    _ ≤ ‖Pgh - Cgh‖ + (‖Cgh - Cg * Ch‖ +
          (‖(Cg - Pg) * Ph‖ + ‖Cg * (Ch - Ph)‖)) := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ ε / 4 + (ε / 4 + (ε / 4 + ε / 4)) :=
        add_le_add hgh (add_le_add hm (add_le_add hcross1 hcross2))
    _ = ε := by ring

/-- The polar-corrected corner unitary is eventually within any tolerance of
the corner compression. -/
theorem cornerUnitary_close_eventually (A : OpAlmostRepresentation G)
    {z : G} (hz : z * z = 1) (hcentral : ∀ g : G, z * g = g * z) (g : G) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(cornerUnitary A z n g :
          Matrix
            {i : A.model n //
              negPredicate
                (A.map n z : Matrix (A.model n) (A.model n) ℂ) i}
            {i : A.model n //
              negPredicate
                (A.map n z : Matrix (A.model n) (A.model n) ℂ) i} ℂ) -
        cornerMicrostate A z n g‖ ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := cornerMicrostate_gram_eventually A hz hcentral g
    (min (ε / 2) (1 / 2)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hb := norm_cornerUnitary_sub_cornerMicrostate A z n g
    (delta := min (ε / 2) (1 / 2)) (by positivity)
    (min_le_right _ _) (hN n hn)
  have hmin : min (ε / 2) (1 / 2) ≤ ε / 2 := min_le_left _ _
  linarith

/-- On the corner, the marked involution's polar-corrected unitary converges
to `-1`. -/
theorem cornerUnitary_involution_eventually (A : OpAlmostRepresentation G)
    {z : G} (hz : z * z = 1) (hcentral : ∀ g : G, z * g = g * z) :
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(cornerUnitary A z n z :
          Matrix
            {i : A.model n //
              negPredicate
                (A.map n z : Matrix (A.model n) (A.model n) ℂ) i}
            {i : A.model n //
              negPredicate
                (A.map n z : Matrix (A.model n) (A.model n) ℂ) i} ℂ) + 1‖
        ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨Ni, hNi⟩ :=
    cornerMicrostate_involution_eventually (z := z) A hz (ε / 2) hhalf
  obtain ⟨Nz, hNz⟩ := cornerUnitary_close_eventually A hz hcentral z
    (ε / 2) hhalf
  refine ⟨max Ni Nz, fun n hn => ?_⟩
  exact norm_add_one_le_of_close
    (cornerMicrostate A z n z) (cornerUnitary A z n z)
    (hNz n ((le_max_right Ni Nz).trans hn))
    (hNi n ((le_max_left Ni Nz).trans hn))

/-- The packaged negative-corner model at a fixed nonemptiness threshold
`N₀`: the coordinates are the corner sites at time `max n N₀` and the maps
are the polar-corrected corner unitaries.  A top-level definition with
`@[simp]` projection lemmas, so consumers rewrite along the projections
instead of unfolding a structure literal. -/
noncomputable def cornerModel (A : OpAlmostRepresentation G) (z : G)
    (hz : z * z = 1) (hcentral : ∀ g : G, z * g = g * z) (N₀ : ℕ)
    (hN₀ : ∀ n ≥ N₀, Nonempty
      {i : A.model n //
        negPredicate (A.map n z : Matrix (A.model n) (A.model n) ℂ) i}) :
    OpAlmostRepresentation G where
  model n :=
    ⟨{i : A.model (max n N₀) //
        negPredicate
          (A.map (max n N₀) z :
            Matrix (A.model (max n N₀)) (A.model (max n N₀)) ℂ) i},
      inferInstance, inferInstance⟩
  modelNonempty n := Fintype.card_pos_iff.mpr (hN₀ _ (le_max_right n N₀))
  map n g := cornerUnitary A z (max n N₀) g
  asymptoticallyMultiplicative := by
    intro g h ε hε
    obtain ⟨Nm, hNm⟩ := cornerMicrostate_multiplicative_eventually A hz
      hcentral g h (ε / 4) (by linarith)
    obtain ⟨Ng, hNg⟩ := cornerUnitary_close_eventually A hz hcentral g
      (ε / 4) (by linarith)
    obtain ⟨Nh, hNh⟩ := cornerUnitary_close_eventually A hz hcentral h
      (ε / 4) (by linarith)
    obtain ⟨Ngh, hNgh⟩ := cornerUnitary_close_eventually A hz hcentral
      (g * h) (ε / 4) (by linarith)
    refine ⟨max (max Nm Ng) (max Nh Ngh), fun n hn => ?_⟩
    have hm : Nm ≤ max n N₀ := le_trans
      ((le_max_left Nm Ng).trans ((le_max_left _ _).trans hn))
      (le_max_left n N₀)
    have hg : Ng ≤ max n N₀ := le_trans
      ((le_max_right Nm Ng).trans ((le_max_left _ _).trans hn))
      (le_max_left n N₀)
    have hh : Nh ≤ max n N₀ := le_trans
      ((le_max_left Nh Ngh).trans ((le_max_right _ _).trans hn))
      (le_max_left n N₀)
    have hgh : Ngh ≤ max n N₀ := le_trans
      ((le_max_right Nh Ngh).trans ((le_max_right _ _).trans hn))
      (le_max_left n N₀)
    exact norm_mul_defect_le_of_close
      (cornerMicrostate A z (max n N₀) g)
      (cornerMicrostate A z (max n N₀) h)
      (cornerMicrostate A z (max n N₀) (g * h))
      (cornerUnitary A z (max n N₀) g)
      (cornerUnitary A z (max n N₀) h)
      (cornerUnitary A z (max n N₀) (g * h))
      (hNgh _ hgh) (hNm _ hm) (hNg _ hg) (hNh _ hh)
      (norm_le_one_of_mem_unitaryGroup (cornerUnitary A z (max n N₀) h).2)
      (norm_cornerMicrostate_le_one A z (max n N₀) g)

@[simp] theorem cornerModel_map (A : OpAlmostRepresentation G) (z : G)
    (hz : z * z = 1) (hcentral : ∀ g : G, z * g = g * z) (N₀ : ℕ)
    (hN₀ : ∀ n ≥ N₀, Nonempty
      {i : A.model n //
        negPredicate (A.map n z : Matrix (A.model n) (A.model n) ℂ) i})
    (n : ℕ) (g : G) :
    (cornerModel A z hz hcentral N₀ hN₀).map n g =
      cornerUnitary A z (max n N₀) g := rfl

/-- **The negative corner of a separated approximate central involution is
an operator-norm almost representation on which the involution converges to
`-1`.**  This is the finite-stage central-corner cut of the non-MF
manuscript: no lower bound on the corner ranks is needed, and no
spectral-gap input enters — leakage is controlled by the exact sign
commutator identity, and exactness of the corner unitaries comes from polar
correction. -/
theorem exists_negativeCorner_opAlmostRepresentation
    (A : OpAlmostRepresentation G) {z : G} (hz : z * z = 1)
    (hcentral : ∀ g : G, z * g = g * z)
    {delta : ℝ} (hdelta : 0 < delta)
    (hsep : ∃ N, ∀ n ≥ N,
      delta ≤ ‖(A.map n z : Matrix (A.model n) (A.model n) ℂ) - A.map n 1‖) :
    ∃ B : OpAlmostRepresentation G,
      ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        ‖(B.map n z : Matrix (B.model n) (B.model n) ℂ) + 1‖ ≤ ε := by
  classical
  obtain ⟨N₀, hN₀⟩ :=
    nonempty_corner_eventually_of_separated A hz hdelta hsep
  refine ⟨cornerModel A z hz hcentral N₀ hN₀, ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := cornerUnitary_involution_eventually A hz hcentral ε hε
  refine ⟨N, fun n hn => ?_⟩
  exact hN (max n N₀) (le_trans hn (le_max_left n N₀))

end NegativeCornerModel
end GroupApproximation
