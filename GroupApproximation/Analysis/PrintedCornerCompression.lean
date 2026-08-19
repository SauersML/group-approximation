import GroupApproximation.Sofic.KazhdanCornerModel

/-!
# Compressing to `q_n M_{d_n}(ℂ) q_n` and polar-correcting

Proof-ledger row `NK.07`, the closing sentence of the compression paragraph of
`thm:abstract-nk`:

> Compressing every model to `q_n M_{d_n}(ℂ) q_n` and polar-correcting now
> yields an operator-norm asymptotic representation `(W_{g,n})` of `H̄` on
> nonzero blocks.

Everything before this sentence is already on the printed objects.
`Analysis/OmegaCoronaKazhdanProjection` lifts `q` to genuine projection
matrices `q_n`, nonzero along `ω` and with `‖[q_n, V_{g,n}]‖ →_ω 0`, and
`Analysis/PrintedDiagonalSubsequence` relabels along the printed `A_j` so that
those statements become ordinary ones.  This file performs the compression the
sentence names, from exactly the data the relabelled sequence supplies:
projection matrices `q_n`, nonzero at every stage, whose commutators with the
models vanish.

## Why the corner is a matrix algebra, and which one

`q_n M_{d_n}(ℂ) q_n ≅ M_{r_n}(ℂ)` is an isomorphism of algebras, not an
equality, and the print uses it as one.  The identification here is the
concrete one: `q_n` is a Hermitian idempotent, so its eigenvalues are `0` and
`1` (`eigenvalues_eq_zero_or_one`), in its own eigenbasis it *is* the indicator
of its eigenvalue-one coordinates (`eigenbasisConj_eq_coordinateProjection`),
and the corner is the principal block on those coordinates.  `cornerModel` is
that coordinate type, and it is nonempty exactly because `q_n ≠ 0` — the
printed "on nonzero blocks".

## The two estimates, and where the commutator enters

Both are instances of the generic block estimates of
`Sofic/KazhdanCornerModel`, and both are driven by one quantity: the norm of
the off-diagonal block of a model in the eigenbasis of `q_n`.  That block is a
two-sided cut between complementary coordinate families, and a two-sided cut is
a commutator (`norm_coordinateBlock_compl_le_commutator`) — which is why
`‖[q_n, V_{g,n}]‖ → 0` is the whole input.

* *Unitarity.*  The Gram defect of a compressed unitary is the square of that
  block (`norm_cornerGram_sub_one_le`), so it vanishes and polar correction
  applies from some stage on.
* *Multiplicativity.*  The compression of a product differs from the product of
  the compressions by the ambient multiplication defect plus the product of two
  such blocks (`norm_cornerCompress_mul_defect_le`).

## The finitely many remaining indices

Polar correction needs the Gram defect at or below `1/2`, which holds only
eventually, so `cornerMap` sets `W_{g,n} = 1` at the stages where it does not.
That is the device the manuscript itself uses at `lem:lift` — "set `u_n = 1` at
the finitely many remaining indices" (row `PRE.11`) — applied here for the same
reason and at the same kind of set: `eventually_gramClose` shows the stages
where the guard fails are a bounded initial segment for each fixed `g`.
-/

namespace GroupApproximation
namespace PrintedCornerCompression

open Filter Topology Matrix
open KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## Cutting a matrix between complementary coordinate families -/

section Cut

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The `0`/`1` diagonal matrix of a coordinate family: the projection onto
those coordinates, written in the coordinates themselves. -/
def coordinateProjection (p : Y → Prop) [DecidablePred p] : Matrix Y Y ℂ :=
  Matrix.diagonal fun i ↦ if p i then (1 : ℂ) else 0

theorem norm_coordinateProjection_le_one (p : Y → Prop) [DecidablePred p] :
    ‖coordinateProjection (Y := Y) p‖ ≤ 1 := by
  rw [coordinateProjection, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦ ?_
  split <;> simp

theorem coordinateProjection_mul_self (p : Y → Prop) [DecidablePred p] :
    coordinateProjection (Y := Y) p * coordinateProjection p
      = coordinateProjection p := by
  rw [coordinateProjection, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hp : p i <;> simp [hp]

theorem coordinateProjection_compl_mul (p : Y → Prop) [DecidablePred p] :
    coordinateProjection (Y := Y) (fun i ↦ ¬ p i) * coordinateProjection p = 0 := by
  rw [coordinateProjection, coordinateProjection, Matrix.diagonal_mul_diagonal]
  rw [show (fun i ↦ (if ¬ p i then (1 : ℂ) else 0) * (if p i then (1 : ℂ) else 0))
      = (0 : Y → ℂ) by funext i; by_cases hp : p i <;> simp [hp]]
  exact Matrix.diagonal_zero

/-- **The `(¬p, p)` block is unchanged by cutting on both sides.** -/
theorem coordinateBlock_compl_eq_cut (p : Y → Prop) [DecidablePred p]
    (C : Matrix Y Y ℂ) :
    coordinateBlock (fun i ↦ ¬ p i) p C
      = coordinateBlock (fun i ↦ ¬ p i) p
          (coordinateProjection (fun i ↦ ¬ p i) * C * coordinateProjection p) := by
  ext i j
  simp only [coordinateBlock, Matrix.toBlock_apply]
  rw [Matrix.mul_assoc, coordinateProjection, coordinateProjection,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp [i.2, j.2]

/-- **A two-sided cut between complementary families is a commutator.**  This
is the one place the printed `‖[q_n, V_{g,n}]‖ → 0` enters, and everything
below is a consequence of it. -/
theorem norm_coordinateBlock_compl_le_commutator (p : Y → Prop) [DecidablePred p]
    (C : Matrix Y Y ℂ) :
    ‖coordinateBlock (fun i ↦ ¬ p i) p C‖
      ≤ ‖C * coordinateProjection p - coordinateProjection p * C‖ := by
  set D : Matrix Y Y ℂ := coordinateProjection p with hD
  set D' : Matrix Y Y ℂ := coordinateProjection (fun i ↦ ¬ p i) with hD'
  have e1 : D' * (C * D) * D = D' * C * D := by
    rw [show D' * (C * D) * D = D' * C * (D * D) by noncomm_ring, hD,
      coordinateProjection_mul_self]
  have e2 : D' * (D * C) * D = 0 := by
    rw [show D' * (D * C) * D = (D' * D) * C * D by noncomm_ring, hD, hD',
      coordinateProjection_compl_mul, Matrix.zero_mul, Matrix.zero_mul]
  have hcut : D' * (C * D - D * C) * D = D' * C * D := by
    rw [Matrix.mul_sub, Matrix.sub_mul, e1, e2, sub_zero]
  calc
    ‖coordinateBlock (fun i ↦ ¬ p i) p C‖
        = ‖coordinateBlock (fun i ↦ ¬ p i) p (D' * (C * D - D * C) * D)‖ := by
          rw [hcut, ← coordinateBlock_compl_eq_cut]
    _ ≤ ‖D' * (C * D - D * C) * D‖ := norm_coordinateBlock_le _ _ _
    _ ≤ ‖D' * (C * D - D * C)‖ * ‖D‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖D'‖ * ‖C * D - D * C‖) * ‖D‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1 * ‖C * D - D * C‖) * 1 := by
        refine mul_le_mul ?_ (norm_coordinateProjection_le_one p) (norm_nonneg _)
          (by positivity)
        exact mul_le_mul_of_nonneg_right
          (norm_coordinateProjection_le_one (fun i ↦ ¬ p i)) (norm_nonneg _)
    _ = ‖C * D - D * C‖ := by ring

end Cut

/-! ## A projection matrix in its own eigenbasis -/

section Eigenbasis

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The printed corner coordinates of a projection matrix: the coordinates on
which it acts as the identity. -/
def cornerPredicate {q : Matrix Y Y ℂ} (hq : q.IsHermitian) (i : Y) : Prop :=
  (1 / 2 : ℝ) < hq.eigenvalues i

instance cornerPredicate_decidable {q : Matrix Y Y ℂ} (hq : q.IsHermitian) :
    DecidablePred (cornerPredicate hq) := Classical.decPred _

/-- The eigenbasis unitary, abbreviated. -/
def eigenUnitary {q : Matrix Y Y ℂ} (hq : q.IsHermitian) : Matrix Y Y ℂ :=
  hq.eigenvectorUnitary

theorem eigenUnitary_conjTranspose_mul {q : Matrix Y Y ℂ} (hq : q.IsHermitian) :
    (eigenUnitary hq)ᴴ * eigenUnitary hq = 1 := by
  have h := Unitary.star_mul_self_of_mem hq.eigenvectorUnitary.2
  rwa [Matrix.star_eq_conjTranspose] at h

theorem eigenUnitary_mul_conjTranspose {q : Matrix Y Y ℂ} (hq : q.IsHermitian) :
    eigenUnitary hq * (eigenUnitary hq)ᴴ = 1 := by
  have h := Unitary.mul_star_self_of_mem hq.eigenvectorUnitary.2
  rwa [Matrix.star_eq_conjTranspose] at h

theorem eigenUnitary_mem {q : Matrix Y Y ℂ} (hq : q.IsHermitian) :
    eigenUnitary hq ∈ Matrix.unitaryGroup Y ℂ := hq.eigenvectorUnitary.2

theorem eigenUnitary_conjTranspose_mem {q : Matrix Y Y ℂ} (hq : q.IsHermitian) :
    (eigenUnitary hq)ᴴ ∈ Matrix.unitaryGroup Y ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  exact Unitary.star_mul_self_of_mem hq.eigenvectorUnitary.2

/-- Conjugation into the eigenbasis of `q`: the printed `Ṽ = U* V U`. -/
def eigenbasisConj {q : Matrix Y Y ℂ} (hq : q.IsHermitian) (C : Matrix Y Y ℂ) :
    Matrix Y Y ℂ :=
  (eigenUnitary hq)ᴴ * C * eigenUnitary hq

/-- Unitary conjugation preserves the operator norm.  `KazhdanCornerMatrices`
proves this for a bundled `FiniteModel`; the corner coordinates here are a
subtype of one, so the estimate is needed over an arbitrary finite index. -/
theorem norm_unitary_conj {U C : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) : ‖U * C * Uᴴ‖ = ‖C‖ := by
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hU
  rw [CStarRing.norm_mul_mem_unitary _ hUstar,
    CStarRing.norm_mem_unitary_mul _ hU]

theorem norm_eigenbasisConj {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    (C : Matrix Y Y ℂ) : ‖eigenbasisConj hq C‖ = ‖C‖ := by
  have h := norm_unitary_conj (U := (eigenUnitary hq)ᴴ) (C := C)
    (eigenUnitary_conjTranspose_mem hq)
  rwa [Matrix.conjTranspose_conjTranspose] at h

theorem eigenbasisConj_conjTranspose {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    (C : Matrix Y Y ℂ) :
    (eigenbasisConj hq C)ᴴ = eigenbasisConj hq Cᴴ := by
  simp only [eigenbasisConj, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem eigenbasisConj_star_mul_self {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    {V : Matrix Y Y ℂ} (hV : Vᴴ * V = 1) :
    (eigenbasisConj hq V)ᴴ * eigenbasisConj hq V = 1 := by
  rw [eigenbasisConj_conjTranspose, eigenbasisConj, eigenbasisConj,
    show ((eigenUnitary hq)ᴴ * Vᴴ * eigenUnitary hq) *
        ((eigenUnitary hq)ᴴ * V * eigenUnitary hq)
      = (eigenUnitary hq)ᴴ * Vᴴ * (eigenUnitary hq * (eigenUnitary hq)ᴴ) * V *
          eigenUnitary hq by noncomm_ring,
    eigenUnitary_mul_conjTranspose]
  rw [show (eigenUnitary hq)ᴴ * Vᴴ * 1 * V * eigenUnitary hq
      = (eigenUnitary hq)ᴴ * (Vᴴ * V) * eigenUnitary hq by noncomm_ring, hV]
  rw [Matrix.mul_one, eigenUnitary_conjTranspose_mul]

/-- The spectral theorem, in the form used below. -/
theorem eigenbasisConj_eq_diagonal {q : Matrix Y Y ℂ} (hq : q.IsHermitian) :
    eigenbasisConj hq q
      = Matrix.diagonal (fun i ↦ ((hq.eigenvalues i : ℝ) : ℂ)) := by
  have hqdiag : q = eigenUnitary hq *
      Matrix.diagonal (fun i ↦ ((hq.eigenvalues i : ℝ) : ℂ)) * (eigenUnitary hq)ᴴ := by
    calc q = Unitary.conjStarAlgAut ℂ _ hq.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hq.eigenvalues)) := hq.spectral_theorem
      _ = eigenUnitary hq *
          Matrix.diagonal (fun i ↦ ((hq.eigenvalues i : ℝ) : ℂ)) *
            (eigenUnitary hq)ᴴ := rfl
  have key : eigenbasisConj hq q
      = (eigenUnitary hq)ᴴ * (eigenUnitary hq *
          Matrix.diagonal (fun i ↦ ((hq.eigenvalues i : ℝ) : ℂ)) *
            (eigenUnitary hq)ᴴ) * eigenUnitary hq := by
    rw [eigenbasisConj, ← hqdiag]
  rw [key, show (eigenUnitary hq)ᴴ * (eigenUnitary hq *
        Matrix.diagonal (fun i ↦ ((hq.eigenvalues i : ℝ) : ℂ)) * (eigenUnitary hq)ᴴ) *
        eigenUnitary hq
      = ((eigenUnitary hq)ᴴ * eigenUnitary hq) *
          Matrix.diagonal (fun i ↦ ((hq.eigenvalues i : ℝ) : ℂ)) *
          ((eigenUnitary hq)ᴴ * eigenUnitary hq) by noncomm_ring,
    eigenUnitary_conjTranspose_mul, Matrix.one_mul, Matrix.mul_one]

/-- **The eigenvalues of a Hermitian idempotent are `0` and `1`.** -/
theorem eigenvalues_eq_zero_or_one {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    (hidem : q * q = q) (i : Y) :
    hq.eigenvalues i = 0 ∨ hq.eigenvalues i = 1 := by
  have hLL : eigenbasisConj hq q * eigenbasisConj hq q = eigenbasisConj hq q := by
    rw [eigenbasisConj,
      show ((eigenUnitary hq)ᴴ * q * eigenUnitary hq) *
          ((eigenUnitary hq)ᴴ * q * eigenUnitary hq)
        = (eigenUnitary hq)ᴴ * q * (eigenUnitary hq * (eigenUnitary hq)ᴴ) * q *
            eigenUnitary hq by noncomm_ring,
      eigenUnitary_mul_conjTranspose]
    rw [show (eigenUnitary hq)ᴴ * q * 1 * q * eigenUnitary hq
        = (eigenUnitary hq)ᴴ * (q * q) * eigenUnitary hq by noncomm_ring, hidem]
  rw [eigenbasisConj_eq_diagonal hq, Matrix.diagonal_mul_diagonal] at hLL
  have hentry : ((hq.eigenvalues i : ℝ) : ℂ) * ((hq.eigenvalues i : ℝ) : ℂ)
      = ((hq.eigenvalues i : ℝ) : ℂ) := by
    have h := congrFun (congrFun hLL i) i
    rwa [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h
  have hreal : hq.eigenvalues i * hq.eigenvalues i = hq.eigenvalues i := by
    exact_mod_cast hentry
  have : hq.eigenvalues i * (hq.eigenvalues i - 1) = 0 := by ring_nf; linarith [hreal]
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- **A projection matrix is the indicator of its corner coordinates, in its
own eigenbasis.**  This is the concrete form of the printed identification
`q_n M_{d_n}(ℂ) q_n ≅ M_{r_n}(ℂ)`. -/
theorem eigenbasisConj_eq_coordinateProjection {q : Matrix Y Y ℂ}
    (hq : q.IsHermitian) (hidem : q * q = q) :
    eigenbasisConj hq q = coordinateProjection (cornerPredicate hq) := by
  rw [eigenbasisConj_eq_diagonal hq, coordinateProjection]
  congr 1
  funext i
  rcases eigenvalues_eq_zero_or_one hq hidem i with h | h
  · rw [h]
    have : ¬ cornerPredicate hq i := by
      simp only [cornerPredicate, h]
      norm_num
    simp [this]
  · rw [h]
    have : cornerPredicate hq i := by
      simp only [cornerPredicate, h]
      norm_num
    simp [this]

/-- **The commutator transports into the eigenbasis.** -/
theorem eigenbasisConj_commutator {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    (hidem : q * q = q) (C : Matrix Y Y ℂ) :
    eigenbasisConj hq C * coordinateProjection (cornerPredicate hq)
        - coordinateProjection (cornerPredicate hq) * eigenbasisConj hq C
      = eigenbasisConj hq (C * q - q * C) := by
  rw [← eigenbasisConj_eq_coordinateProjection hq hidem]
  simp only [eigenbasisConj]
  rw [show ((eigenUnitary hq)ᴴ * C * eigenUnitary hq) *
        ((eigenUnitary hq)ᴴ * q * eigenUnitary hq)
      = (eigenUnitary hq)ᴴ * C * (eigenUnitary hq * (eigenUnitary hq)ᴴ) * q *
          eigenUnitary hq by noncomm_ring,
    show ((eigenUnitary hq)ᴴ * q * eigenUnitary hq) *
        ((eigenUnitary hq)ᴴ * C * eigenUnitary hq)
      = (eigenUnitary hq)ᴴ * q * (eigenUnitary hq * (eigenUnitary hq)ᴴ) * C *
          eigenUnitary hq by noncomm_ring,
    eigenUnitary_mul_conjTranspose, Matrix.mul_sub, Matrix.sub_mul]
  noncomm_ring

/-- **The off-diagonal block of a model is bounded by its commutator with the
projection.**  The printed input, in the form the compression consumes. -/
theorem norm_coordinateBlock_compl_le {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    (hidem : q * q = q) (C : Matrix Y Y ℂ) :
    ‖coordinateBlock (fun i ↦ ¬ cornerPredicate hq i) (cornerPredicate hq)
        (eigenbasisConj hq C)‖ ≤ ‖C * q - q * C‖ := by
  refine (norm_coordinateBlock_compl_le_commutator (cornerPredicate hq)
    (eigenbasisConj hq C)).trans ?_
  rw [eigenbasisConj_commutator hq hidem C, norm_eigenbasisConj]

/-- The block on the other side of the diagonal, bounded by the same
quantity: conjugate transposition swaps the two and fixes `q`. -/
theorem norm_coordinateBlock_self_le {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    (hidem : q * q = q) (C : Matrix Y Y ℂ) :
    ‖coordinateBlock (cornerPredicate hq) (fun i ↦ ¬ cornerPredicate hq i)
        (eigenbasisConj hq C)‖ ≤ ‖C * q - q * C‖ := by
  have hswap : coordinateBlock (cornerPredicate hq)
      (fun i ↦ ¬ cornerPredicate hq i) (eigenbasisConj hq C)
      = (coordinateBlock (fun i ↦ ¬ cornerPredicate hq i) (cornerPredicate hq)
          (eigenbasisConj hq Cᴴ))ᴴ := by
    rw [coordinateBlock_conjTranspose, eigenbasisConj_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
  rw [hswap, Matrix.l2_opNorm_conjTranspose]
  refine (norm_coordinateBlock_compl_le hq hidem Cᴴ).trans_eq ?_
  have hqH : qᴴ = q := hq
  have : Cᴴ * q - q * Cᴴ = -((C * q - q * C)ᴴ) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hqH]
    abel
  rw [this, norm_neg, Matrix.l2_opNorm_conjTranspose]

end Eigenbasis

/-! ## The compression, and its two estimates -/

section Compression

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- **The printed compression** of a matrix to the corner `q M q`, written in
the corner coordinates. -/
def cornerCompression {q : Matrix Y Y ℂ} (hq : q.IsHermitian) (C : Matrix Y Y ℂ) :
    Matrix {i : Y // cornerPredicate hq i} {i : Y // cornerPredicate hq i} ℂ :=
  principalBlock (cornerPredicate hq) (eigenbasisConj hq C)

theorem norm_cornerCompression_le {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    (C : Matrix Y Y ℂ) : ‖cornerCompression hq C‖ ≤ ‖C‖ :=
  (norm_principalBlock_le _ _).trans_eq (norm_eigenbasisConj hq C)

/-- **The Gram defect of a compressed unitary is the square of its
off-diagonal block**, hence at most the square of the printed commutator. -/
theorem norm_cornerGram_sub_one_le {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    (hidem : q * q = q) {V : Matrix Y Y ℂ} (hV : Vᴴ * V = 1) :
    ‖cornerGram (cornerCompression hq V) - 1‖ ≤ ‖V * q - q * V‖ ^ 2 := by
  refine (norm_principalBlock_gram_sub_one_le (cornerPredicate hq)
    (eigenbasisConj hq V) (eigenbasisConj_star_mul_self hq hV)).trans ?_
  have hb := norm_coordinateBlock_compl_le hq hidem V
  have hnn := norm_nonneg (coordinateBlock (fun i ↦ ¬ cornerPredicate hq i)
    (cornerPredicate hq) (eigenbasisConj hq V))
  nlinarith

/-- **The multiplicativity defect of the compression**: the ambient defect plus
the product of the two off-diagonal blocks, which is the generic principal-block
estimate specialized to this corner. -/
theorem norm_cornerCompression_mul_defect_le {q : Matrix Y Y ℂ}
    (hq : q.IsHermitian) (hidem : q * q = q) (A B C : Matrix Y Y ℂ) :
    ‖cornerCompression hq A - cornerCompression hq B * cornerCompression hq C‖
      ≤ ‖A - B * C‖ + ‖B * q - q * B‖ * ‖C * q - q * C‖ := by
  have hbase : ‖cornerCompression hq A
        - cornerCompression hq B * cornerCompression hq C‖
      ≤ ‖eigenbasisConj hq A - eigenbasisConj hq B * eigenbasisConj hq C‖
        + ‖coordinateBlock (cornerPredicate hq) (fun i ↦ ¬ cornerPredicate hq i)
              (eigenbasisConj hq B)‖
          * ‖coordinateBlock (fun i ↦ ¬ cornerPredicate hq i) (cornerPredicate hq)
              (eigenbasisConj hq C)‖ :=
    norm_principalBlock_mul_defect_le (cornerPredicate hq)
      (eigenbasisConj hq A) (eigenbasisConj hq B) (eigenbasisConj hq C)
  have hdefect : eigenbasisConj hq A - eigenbasisConj hq B * eigenbasisConj hq C
      = eigenbasisConj hq (A - B * C) := by
    simp only [eigenbasisConj]
    exact unitaryConjugation_mul_defect_eq (U := eigenUnitary hq)
      (eigenUnitary_mul_conjTranspose hq)
  rw [hdefect, norm_eigenbasisConj] at hbase
  have hblocks := mul_le_mul (norm_coordinateBlock_self_le hq hidem B)
    (norm_coordinateBlock_compl_le hq hidem C) (norm_nonneg _) (norm_nonneg _)
  linarith

/-- **Correcting two factors and their product moves a multiplication defect by
at most the sum of the three corrections.**  Stated once, over an arbitrary
finite index, because the assembly below applies it to expressions large enough
that unifying them term by term is expensive. -/
theorem norm_sub_mul_le_of_corrections {a b c a' b' c' : Matrix Y Y ℂ}
    (hc : ‖c‖ ≤ 1) (hb' : ‖b'‖ ≤ 1) :
    ‖a' - b' * c'‖ ≤ ‖a' - a‖ + ‖a - b * c‖ + (‖b' - b‖ + ‖c' - c‖) := by
  have hsplit : a' - b' * c' = (a' - a) + (a - b * c) + (b * c - b' * c') := by abel
  have hcross : b * c - b' * c' = (b - b') * c + b' * (c - c') := by noncomm_ring
  have h1 : ‖(b - b') * c‖ ≤ ‖b - b'‖ * ‖c‖ := Matrix.l2_opNorm_mul _ _
  have h2 : ‖b' * (c - c')‖ ≤ ‖b'‖ * ‖c - c'‖ := Matrix.l2_opNorm_mul _ _
  have h3 : ‖b * c - b' * c'‖ ≤ ‖b - b'‖ * ‖c‖ + ‖b'‖ * ‖c - c'‖ := by
    rw [hcross]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  have h4 : ‖b - b'‖ * ‖c‖ ≤ ‖b' - b‖ * 1 := by
    rw [norm_sub_rev]
    exact mul_le_mul_of_nonneg_left hc (norm_nonneg _)
  have h5 : ‖b'‖ * ‖c - c'‖ ≤ 1 * ‖c' - c‖ := by
    rw [norm_sub_rev]
    exact mul_le_mul_of_nonneg_right hb' (norm_nonneg _)
  have h6 : ‖(a' - a) + (a - b * c) + (b * c - b' * c')‖
      ≤ ‖a' - a‖ + ‖a - b * c‖ + ‖b * c - b' * c'‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  rw [hsplit]
  nlinarith [norm_nonneg (a' - a), norm_nonneg (a - b * c)]

/-- **The corner is nonempty exactly when the projection is nonzero.**  This is
the printed "on nonzero blocks". -/
theorem cornerPredicate_exists {q : Matrix Y Y ℂ} (hq : q.IsHermitian)
    (hidem : q * q = q) (hne : q ≠ 0) : ∃ i, cornerPredicate hq i := by
  by_contra hcon
  have hcon' : ∀ i, ¬ cornerPredicate hq i := fun i hi ↦ hcon ⟨i, hi⟩
  refine hne ?_
  have hzero : eigenbasisConj hq q = 0 := by
    rw [eigenbasisConj_eq_coordinateProjection hq hidem, coordinateProjection]
    rw [show (fun i ↦ if cornerPredicate hq i then (1 : ℂ) else 0) = (0 : Y → ℂ) by
      funext i; simp [hcon' i]]
    exact Matrix.diagonal_zero
  have : (eigenUnitary hq) * eigenbasisConj hq q * (eigenUnitary hq)ᴴ = q := by
    rw [eigenbasisConj,
      show eigenUnitary hq * ((eigenUnitary hq)ᴴ * q * eigenUnitary hq) *
          (eigenUnitary hq)ᴴ
        = (eigenUnitary hq * (eigenUnitary hq)ᴴ) * q *
            (eigenUnitary hq * (eigenUnitary hq)ᴴ) by noncomm_ring,
      eigenUnitary_mul_conjTranspose, Matrix.one_mul, Matrix.mul_one]
  rw [← this, hzero, Matrix.mul_zero, Matrix.zero_mul]

end Compression

/-! ## The printed asymptotic representation on the nonzero blocks -/

section Assembly

variable {G : Type*} [Group G]

/-- The data the relabelled sequence of the printed proof supplies: models,
unitaries whose multiplication defects vanish in the ordinary sense, and
projection matrices, nonzero at every stage, whose commutators with the
unitaries vanish in the ordinary sense.

Every field is a printed clause.  Nothing is assumed about how the projections
arose: `Analysis/OmegaCoronaKazhdanProjection` produces them from the corona
and `Analysis/PrintedDiagonalSubsequence` converts the `ω`-statements into the
`atTop`-statements below, which is exactly the printed relabelling. -/
structure PrintedCornerData (G : Type*) [Group G] (model : ℕ → FiniteModel) where
  /-- The models `V_{g,n}`. -/
  V : ∀ n, G → Matrix.unitaryGroup (model n) ℂ
  /-- The printed projections `q_n`. -/
  q : ∀ n, Matrix (model n) (model n) ℂ
  /-- They are genuine orthogonal projections, not approximate ones. -/
  q_projection : ∀ n, IsOrthogonalProjectionMatrix (q n)
  /-- The printed "nonzero along `ω`", after the relabelling. -/
  q_ne_zero : ∀ n, q n ≠ 0
  /-- `(V_{g,n})` is an operator-norm asymptotic representation. -/
  mul_vanishing : ∀ g h : G, Tendsto (fun n ↦
    ‖(V n (g * h) : Matrix (model n) (model n) ℂ) -
      (V n g : Matrix (model n) (model n) ℂ) * V n h‖) atTop (𝓝 0)
  /-- The printed `‖[q_n, V_{g,n}]‖ → 0`, after the relabelling. -/
  commutator_vanishing : ∀ g : G, Tendsto (fun n ↦
    ‖(V n g : Matrix (model n) (model n) ℂ) * q n -
      q n * (V n g : Matrix (model n) (model n) ℂ)‖) atTop (𝓝 0)

namespace PrintedCornerData

variable {model : ℕ → FiniteModel} (D : PrintedCornerData G model)

theorem qHermitian (n : ℕ) : (D.q n).IsHermitian := (D.q_projection n).1

theorem qIdem (n : ℕ) : D.q n * D.q n = D.q n := (D.q_projection n).2

/-- **The printed corner `q_n M_{d_n}(ℂ) q_n`**, as an honest finite matrix
model. -/
abbrev cornerModel (n : ℕ) : FiniteModel :=
  ⟨{i : model n // cornerPredicate (D.qHermitian n) i}, inferInstance,
    inferInstance⟩

/-- **The blocks are nonzero.** -/
theorem cornerModel_card_pos (n : ℕ) : 0 < Fintype.card (D.cornerModel n) := by
  obtain ⟨i, hi⟩ := cornerPredicate_exists (D.qHermitian n) (D.qIdem n) (D.q_ne_zero n)
  exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩

/-- The ambient model is nonempty wherever the corner is, which is everywhere. -/
theorem model_nonempty (D : PrintedCornerData G model) (n : ℕ) :
    Nonempty (model n) := by
  obtain ⟨i, -⟩ := cornerPredicate_exists (D.qHermitian n) (D.qIdem n) (D.q_ne_zero n)
  exact ⟨i⟩

/-- The uncorrected compression `q_n V_{g,n} q_n`, in the corner coordinates. -/
def compress (n : ℕ) (g : G) :
    Matrix (D.cornerModel n) (D.cornerModel n) ℂ :=
  cornerCompression (D.qHermitian n) ((D.V n g : Matrix (model n) (model n) ℂ))

theorem norm_compress_le_one (n : ℕ) (g : G) : ‖D.compress n g‖ ≤ 1 := by
  letI : Nonempty (model n) := D.model_nonempty n
  refine (norm_cornerCompression_le _ _).trans_eq ?_
  exact CStarRing.norm_of_mem_unitary (D.V n g).2

/-- The printed commutator, abbreviated. -/
def commutatorNorm (n : ℕ) (g : G) : ℝ :=
  ‖(D.V n g : Matrix (model n) (model n) ℂ) * D.q n -
    D.q n * (D.V n g : Matrix (model n) (model n) ℂ)‖

theorem commutatorNorm_tendsto (g : G) :
    Tendsto (fun n ↦ D.commutatorNorm n g) atTop (𝓝 0) := D.commutator_vanishing g

theorem V_conjTranspose_mul_self (n : ℕ) (g : G) :
    ((D.V n g : Matrix (model n) (model n) ℂ))ᴴ *
      (D.V n g : Matrix (model n) (model n) ℂ) = 1 := by
  have h := (D.V n g).2
  rw [Matrix.mem_unitaryGroup_iff'] at h
  rwa [Matrix.star_eq_conjTranspose] at h

theorem norm_cornerGram_compress_le (n : ℕ) (g : G) :
    ‖cornerGram (D.compress n g) - 1‖ ≤ (D.commutatorNorm n g) ^ 2 :=
  norm_cornerGram_sub_one_le (D.qHermitian n) (D.qIdem n)
    (D.V_conjTranspose_mul_self n g)

/-- The stages where polar correction applies: for a fixed `g` the guard fails
only finitely often, because the Gram defect is bounded by the square of a
vanishing quantity. -/
theorem eventually_gramClose (g : G) :
    ∀ᶠ n in atTop, ‖cornerGram (D.compress n g) - 1‖ ≤ (1 / 2 : ℝ) := by
  have hsq : Tendsto (fun n ↦ (D.commutatorNorm n g) ^ 2) atTop (𝓝 0) := by
    have := (D.commutatorNorm_tendsto g).pow 2
    simpa using this
  have h : ∀ᶠ n in atTop, (D.commutatorNorm n g) ^ 2 ≤ (1 / 2 : ℝ) := by
    exact hsq.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  exact h.mono fun n hn ↦ (D.norm_cornerGram_compress_le n g).trans hn

/-- **The printed `(W_{g,n})`**: the polar correction of the compression where
the Gram defect allows it, and `1` at the remaining stages — the device the
manuscript uses at `lem:lift`. -/
def cornerMap (n : ℕ) (g : G) : Matrix.unitaryGroup (D.cornerModel n) ℂ :=
  if h : ‖cornerGram (D.compress n g) - 1‖ ≤ (1 / 2 : ℝ) then
    polarCorrectUnitary (D.compress n g) (cornerGram_isHermitian _) le_rfl h
  else 1

theorem cornerMap_eq_of_gramClose {n : ℕ} {g : G}
    (h : ‖cornerGram (D.compress n g) - 1‖ ≤ (1 / 2 : ℝ)) :
    (D.cornerMap n g : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
      = polarCorrect (D.compress n g) (cornerGram_isHermitian _) := by
  rw [cornerMap, dif_pos h]
  rfl

/-- **Polar correction moves the compression by at most twice its Gram
defect**, at every stage where it is applied. -/
theorem norm_cornerMap_sub_compress_le {n : ℕ} {g : G}
    (h : ‖cornerGram (D.compress n g) - 1‖ ≤ (1 / 2 : ℝ)) :
    ‖(D.cornerMap n g : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
        - D.compress n g‖ ≤ 2 * ‖cornerGram (D.compress n g) - 1‖ := by
  rw [D.cornerMap_eq_of_gramClose h]
  exact norm_polarCorrect_sub_le (D.compress n g) (cornerGram_isHermitian _)
    (D.norm_compress_le_one n g) (norm_nonneg _) h le_rfl

/-- **The polar correction is asymptotically the compression.** -/
theorem cornerMap_sub_compress_tendsto (g : G) :
    Tendsto (fun n ↦
      ‖(D.cornerMap n g : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
        - D.compress n g‖) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n ↦ 2 * (D.commutatorNorm n g) ^ 2) atTop (𝓝 0) := by
    have := ((D.commutatorNorm_tendsto g).pow 2).const_mul (2 : ℝ)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ hsq
  refine (D.eventually_gramClose g).mono fun n hn ↦ ?_
  refine (D.norm_cornerMap_sub_compress_le hn).trans ?_
  exact mul_le_mul_of_nonneg_left (D.norm_cornerGram_compress_le n g) (by norm_num)

theorem norm_cornerMap_le_one (n : ℕ) (g : G) :
    ‖(D.cornerMap n g : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)‖ ≤ 1 := by
  letI : Nonempty (D.cornerModel n) := Fintype.card_pos_iff.mp (D.cornerModel_card_pos n)
  exact le_of_eq (CStarRing.norm_of_mem_unitary (D.cornerMap n g).2)

/-- **The compressions are asymptotically multiplicative.** -/
theorem compress_mul_defect_tendsto (g h : G) :
    Tendsto (fun n ↦ ‖D.compress n (g * h) - D.compress n g * D.compress n h‖)
      atTop (𝓝 0) := by
  have hbound : ∀ n, ‖D.compress n (g * h) - D.compress n g * D.compress n h‖
      ≤ ‖(D.V n (g * h) : Matrix (model n) (model n) ℂ) -
            (D.V n g : Matrix (model n) (model n) ℂ) * D.V n h‖
        + D.commutatorNorm n g * D.commutatorNorm n h := fun n ↦
    norm_cornerCompression_mul_defect_le (D.qHermitian n) (D.qIdem n) _ _ _
  have hlim : Tendsto (fun n ↦
      ‖(D.V n (g * h) : Matrix (model n) (model n) ℂ) -
          (D.V n g : Matrix (model n) (model n) ℂ) * D.V n h‖
        + D.commutatorNorm n g * D.commutatorNorm n h) atTop (𝓝 0) := by
    have := (D.mul_vanishing g h).add
      ((D.commutatorNorm_tendsto g).mul (D.commutatorNorm_tendsto h))
    simpa using this
  exact squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _)
    (Eventually.of_forall hbound) hlim

/-- **The corrected corner models are asymptotically multiplicative.**  This is
the printed conclusion: the corrections and the uncorrected multiplication
defect all vanish, so the corrected models multiply in the limit. -/
theorem cornerMap_mul_defect_tendsto (g h : G) :
    Tendsto (fun n ↦
      ‖(D.cornerMap n (g * h) : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
        - (D.cornerMap n g : Matrix (D.cornerModel n) (D.cornerModel n) ℂ) *
          D.cornerMap n h‖) atTop (𝓝 0) := by
  have hbound : ∀ n, ‖(D.cornerMap n (g * h) :
        Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
        - (D.cornerMap n g : Matrix (D.cornerModel n) (D.cornerModel n) ℂ) *
          D.cornerMap n h‖
      ≤ ‖(D.cornerMap n (g * h) : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
            - D.compress n (g * h)‖
        + ‖D.compress n (g * h) - D.compress n g * D.compress n h‖
        + (‖(D.cornerMap n g : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
              - D.compress n g‖
            + ‖(D.cornerMap n h : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
              - D.compress n h‖) := fun n ↦
    norm_sub_mul_le_of_corrections (D.norm_compress_le_one n h)
      (D.norm_cornerMap_le_one n g)
  have hlim : Tendsto (fun n ↦
      ‖(D.cornerMap n (g * h) : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
          - D.compress n (g * h)‖
        + ‖D.compress n (g * h) - D.compress n g * D.compress n h‖
        + (‖(D.cornerMap n g : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
              - D.compress n g‖
            + ‖(D.cornerMap n h : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
              - D.compress n h‖)) atTop (𝓝 0) := by
    have := ((D.cornerMap_sub_compress_tendsto (g * h)).add
      (D.compress_mul_defect_tendsto g h)).add
        ((D.cornerMap_sub_compress_tendsto g).add
          (D.cornerMap_sub_compress_tendsto h))
    simpa using this
  exact squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _)
    (Eventually.of_forall hbound) hlim

/-- **`NK.07`'s closing sentence.**

> Compressing every model to `q_n M_{d_n}(ℂ) q_n` and polar-correcting now
> yields an operator-norm asymptotic representation `(W_{g,n})` of `H̄` on
> nonzero blocks.

The models are the corners of the printed projections, they are nonzero at
every stage, and the maps are the polar corrections of the printed
compressions. -/
def cornerRepresentation : OpAlmostRepresentation G where
  model := D.cornerModel
  modelNonempty := D.cornerModel_card_pos
  map := D.cornerMap
  asymptoticallyMultiplicative := by
    intro g h ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (D.cornerMap_mul_defect_tendsto g h) ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have := hN n hn
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le

theorem cornerRepresentation_model (n : ℕ) :
    D.cornerRepresentation.model n = D.cornerModel n := rfl

/-! `cornerRepresentation.map` is `cornerMap` by definition -- the structure
instance above is where that is written -- so the statements below are phrased
with `cornerMap`, whose type mentions the corner model directly. -/

/-- **The printed sentence, whole.**  The compressions to the corners
`q_n M_{d_n}(ℂ) q_n`, polar-corrected, form an operator-norm asymptotic
representation — `cornerRepresentation` is that representation, and it is an
`OpAlmostRepresentation` by construction, which is the definition the
manuscript's "operator-norm asymptotic representation" names.  Its models are
the printed corners; every one of them is nonzero, which is the printed "on
nonzero blocks"; and the polar correction is asymptotically invisible, so the
representation *is* the compression in the limit. -/
theorem manuscriptCornerAsymptoticRepresentation :
    (∀ n, D.cornerRepresentation.model n = D.cornerModel n) ∧
      (∀ n, 0 < Fintype.card (D.cornerModel n)) ∧
      (∀ g : G, Tendsto (fun n ↦
        ‖(D.cornerMap n g : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
          - D.compress n g‖) atTop (𝓝 0)) :=
  ⟨fun _ ↦ rfl, D.cornerModel_card_pos, D.cornerMap_sub_compress_tendsto⟩

end PrintedCornerData

/-- **`lem:corner`, the printed lemma, in one statement.**

> Let `H` be a group, let `V_{g,n} ∈ U(d_n)` be an operator-norm asymptotic
> representation of `H`, and let `q_n ∈ M_{d_n}(ℂ)` be nonzero projections with
> `‖[q_n, V_{g,n}]‖ → 0` for every `g ∈ H`.  Write `r_n = rank q_n ≥ 1` and
> identify `q_n M_{d_n}(ℂ) q_n ≅ M_{r_n}(ℂ)`.  Then there are unitaries
> `W_{g,n} ∈ U(r_n)` with `‖W_{g,n} − q_n V_{g,n} q_n‖ → 0` for every `g ∈ H`,
> and `(W_{g,n})` is an operator-norm asymptotic representation of `H` on the
> corners.

The hypotheses are `PrintedCornerData`, field for field.  The conclusion is the
printed one: an `OpAlmostRepresentation` — this development's definition of
"operator-norm asymptotic representation" — whose models are the corners
`q_n M_{d_n}(ℂ) q_n`, every one of them nonzero, so `r_n ≥ 1`; whose unitaries
are the `W_{g,n}`; and whose distance from the compressions `q_n V_{g,n} q_n`
tends to `0`. -/
theorem manuscriptCornerAsymptoticRepresentation {G : Type*} [Group G]
    {model : ℕ → FiniteModel} (D : PrintedCornerData G model) :
    ∃ W : OpAlmostRepresentation G,
      W.model = D.cornerModel ∧
        (∀ n, 0 < Fintype.card (D.cornerModel n)) ∧
        (∀ n g, HEq (W.map n g) (D.cornerMap n g)) ∧
        (∀ g : G, Tendsto (fun n ↦
          ‖(D.cornerMap n g : Matrix (D.cornerModel n) (D.cornerModel n) ℂ)
            - D.compress n g‖) atTop (𝓝 0)) :=
  ⟨D.cornerRepresentation, rfl, D.cornerModel_card_pos,
    fun _ _ ↦ HEq.rfl, D.cornerMap_sub_compress_tendsto⟩

end Assembly

end

end PrintedCornerCompression
end GroupApproximation
