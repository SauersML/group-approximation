import GroupApproximation.Analysis.CStarKOne
import GroupApproximation.Analysis.CStarSymmetryComponent
import GroupApproximation.KTheory.BlockMoves

/-!
# The Whitehead lemma: `K_1` of a unital C-star algebra is abelian

Fix `u v` in `U(M_n(A))` and pass to level `n + n`.  Write

    U = diag (u, 1),   V = diag (v, 1),   V' = diag (1, v).

Two facts do everything:

* block sums multiply blockwise (`KTheory.blockSum_mul_blockSum`), so
  `U * V' = diag (u, v) = V' * U`;
* the block swap `S` of `M_{n+n}(A)` is a *self-adjoint* unitary, hence lies in `U_0`
  (`mem_unitaryComponentOne_of_isSelfAdjoint`), and conjugating by it carries `V` to `V'`.

Since `[S] = 1` in `U/U_0`, the second fact gives `[V'] = [V]`, and then

    [U][V] = [U][V'] = [U V'] = [V' U] = [V'][U] = [V][U].

Pushing `[u]` and `[v]` from level `n` to level `n + n` therefore makes them commute, and by
`GroupTower.commGroup_of_forall_commute` the colimit `K_1(A)` is abelian.

No rotation homotopy, no elementary-matrix factorisation and no exponential of an algebra
element appears.  The only analytic input is that a symmetry `1 - 2p` is connected to `1`
through the unitaries `1 + (e^{iπt} - 1) p`, which is `Analysis/CStarSymmetryComponent`.
-/

namespace GroupApproximation

open KTheory

universe u

noncomputable section

/-! ## The block swap of the index set -/

theorem finSumSwap_involutive (n : ℕ) (i : Fin (n + n)) :
    finSumSwap n n (finSumSwap n n i) = i := by
  induction i using Fin.addCases with
  | left a => rw [finSumSwap_castAdd, finSumSwap_natAdd]
  | right b => rw [finSumSwap_natAdd, finSumSwap_castAdd]

theorem finSumSwap_symm_self (n : ℕ) : (finSumSwap n n).symm = finSumSwap n n := by
  ext i
  apply (finSumSwap n n).injective
  rw [Equiv.apply_symm_apply, finSumSwap_involutive]

section Algebra

variable {A : Type u} [CStarAlgebra A]

/-! ## Permutation matrices -/

variable (A) in
/-- The permutation matrix of a bijection of the index set: `1` in position `(i, e i)`. -/
def permMat {N : ℕ} (e : Fin N ≃ Fin N) : CStarMat N A :=
  fun i j => if j = e i then 1 else 0

theorem permMat_apply {N : ℕ} (e : Fin N ≃ Fin N) (i j : Fin N) :
    permMat A e i j = if j = e i then 1 else 0 := rfl

theorem permMat_mul_matrix {N : ℕ} (e : Fin N ≃ Fin N) (M : CStarMat N A) :
    permMat A e * M = M.submatrix e id := by
  ext i j
  rw [CStarMatrix.mul_apply, Finset.sum_eq_single (e i)]
  · rw [permMat_apply, if_pos rfl, one_mul]
    rfl
  · intro b _ hb
    rw [permMat_apply, if_neg hb, zero_mul]
  · intro hc
    exact absurd (Finset.mem_univ (e i)) hc

theorem matrix_mul_permMat {N : ℕ} (e : Fin N ≃ Fin N) (M : CStarMat N A) :
    M * permMat A e.symm = M.submatrix id e := by
  ext i j
  rw [CStarMatrix.mul_apply, Finset.sum_eq_single (e j)]
  · rw [permMat_apply, if_pos (Equiv.symm_apply_apply e j).symm, mul_one]
    rfl
  · intro b _ hb
    rw [permMat_apply, if_neg, mul_zero]
    intro hc
    exact hb (by rw [hc, Equiv.apply_symm_apply])
  · intro hc
    exact absurd (Finset.mem_univ (e j)) hc

theorem star_permMat {N : ℕ} (e : Fin N ≃ Fin N) :
    star (permMat A e) = permMat A e.symm := by
  ext i j
  rw [CStarMatrix.star_apply, permMat_apply, permMat_apply]
  by_cases h : i = e j
  · rw [if_pos h, star_one, if_pos (by rw [h, Equiv.symm_apply_apply])]
  · rw [if_neg h, star_zero, if_neg]
    intro hc
    exact h (by rw [hc, Equiv.apply_symm_apply])

theorem permMat_mem_unitary {N : ℕ} (e : Fin N ≃ Fin N) :
    permMat A e ∈ unitary (CStarMat N A) := by
  constructor
  · rw [star_permMat, permMat_mul_matrix]
    ext i j
    rw [Matrix.submatrix_apply, id_eq, permMat_apply, Equiv.apply_symm_apply,
      CStarMatrix.one_apply]
    by_cases h : i = j
    · rw [if_pos h.symm, if_pos h]
    · rw [if_neg (fun hc => h hc.symm), if_neg h]
  · rw [star_permMat, matrix_mul_permMat]
    ext i j
    rw [Matrix.submatrix_apply, id_eq, permMat_apply, CStarMatrix.one_apply]
    by_cases h : i = j
    · rw [if_pos (by rw [h]), if_pos h]
    · rw [if_neg (fun hc => h (e.injective hc).symm), if_neg h]

theorem isSelfAdjoint_permMat {N : ℕ} {e : Fin N ≃ Fin N} (he : e.symm = e) :
    IsSelfAdjoint (permMat A e) := by
  show star (permMat A e) = permMat A e
  rw [star_permMat, he]

/-- Conjugating a matrix by a permutation matrix reindexes it. -/
theorem permMat_conj {N : ℕ} (e : Fin N ≃ Fin N) (M : CStarMat N A) :
    permMat A e * M * permMat A e.symm = M.submatrix e e := by
  rw [permMat_mul_matrix, matrix_mul_permMat]
  rfl

/-! ## Block sums of unitaries -/

theorem blockSum_one_one (m n : ℕ) :
    blockSum (1 : CStarMat m A) (1 : CStarMat n A) = (1 : CStarMat (m + n) A) := by
  ext i j
  induction i using Fin.addCases with
  | left a =>
    induction j using Fin.addCases with
    | left b =>
      rw [blockSum_apply_castAdd_castAdd, CStarMatrix.one_apply, CStarMatrix.one_apply]
      by_cases h : a = b
      · rw [if_pos h, if_pos (by rw [h])]
      · refine (if_neg h).trans (if_neg ?_).symm
        intro hc
        refine h (Fin.eq_of_val_eq ?_)
        have hval := congrArg Fin.val hc
        simpa using hval
    | right b =>
      rw [blockSum_apply_castAdd_natAdd, CStarMatrix.one_apply, if_neg]
      intro hc
      have ha := a.isLt
      have hval := congrArg Fin.val hc
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at hval
      omega
  | right a =>
    induction j using Fin.addCases with
    | left b =>
      rw [blockSum_apply_natAdd_castAdd, CStarMatrix.one_apply, if_neg]
      intro hc
      have hb := b.isLt
      have hval := congrArg Fin.val hc
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at hval
      omega
    | right b =>
      rw [blockSum_apply_natAdd_natAdd, CStarMatrix.one_apply, CStarMatrix.one_apply]
      by_cases h : a = b
      · rw [if_pos h, if_pos (by rw [h])]
      · refine (if_neg h).trans (if_neg ?_).symm
        intro hc
        refine h (Fin.eq_of_val_eq ?_)
        have hval := congrArg Fin.val hc
        simp only [Fin.coe_natAdd] at hval
        omega

/-- The block sum of two unitaries. -/
def blockSumU {m n : ℕ} (x : unitary (CStarMat m A)) (y : unitary (CStarMat n A)) :
    unitary (CStarMat (m + n) A) :=
  ⟨blockSum (x : CStarMat m A) (y : CStarMat n A), by
    refine ⟨?_, ?_⟩
    · rw [star_blockSum, blockSum_mul_blockSum, x.2.1, y.2.1, blockSum_one_one]
    · rw [star_blockSum, blockSum_mul_blockSum, x.2.2, y.2.2, blockSum_one_one]⟩

@[simp] theorem coe_blockSumU {m n : ℕ} (x : unitary (CStarMat m A))
    (y : unitary (CStarMat n A)) :
    ((blockSumU x y : unitary (CStarMat (m + n) A)) : CStarMat (m + n) A)
      = blockSum (x : CStarMat m A) (y : CStarMat n A) := rfl

theorem blockSumU_mul {m n : ℕ} (x₁ x₂ : unitary (CStarMat m A))
    (y₁ y₂ : unitary (CStarMat n A)) :
    blockSumU x₁ y₁ * blockSumU x₂ y₂ = blockSumU (x₁ * x₂) (y₁ * y₂) :=
  Subtype.ext (blockSum_mul_blockSum _ _ _ _)

/-! ## The bridge from `blockOne` to `blockSum` -/

theorem blockOne_eq_blockSum {n : ℕ} (M : CStarMat n A) (m : ℕ) :
    blockOne M (n + m) = blockSum M (1 : CStarMat m A) := by
  ext i j
  induction i using Fin.addCases with
  | left a =>
    have hia : ((Fin.castAdd m a : Fin (n + m)) : ℕ) < n := by simpa using a.isLt
    induction j using Fin.addCases with
    | left b =>
      have hjb : ((Fin.castAdd m b : Fin (n + m)) : ℕ) < n := by simpa using b.isLt
      rw [blockOne_apply_of_lt_of_lt M _ _ hia hjb, blockSum_apply_castAdd_castAdd]
    | right b =>
      have hjb : ¬ (((Fin.natAdd n b : Fin (n + m)) : ℕ) < n) := by
        simp only [Fin.coe_natAdd]; omega
      rw [blockOne_apply_of_lt_of_not_lt M _ _ hia hjb, blockSum_apply_castAdd_natAdd]
  | right a =>
    have hia : ¬ (((Fin.natAdd n a : Fin (n + m)) : ℕ) < n) := by
      simp only [Fin.coe_natAdd]; omega
    induction j using Fin.addCases with
    | left b =>
      have hjb : ((Fin.castAdd m b : Fin (n + m)) : ℕ) < n := by simpa using b.isLt
      rw [blockOne_apply_of_not_lt_of_lt M _ _ hia hjb, blockSum_apply_natAdd_castAdd]
    | right b =>
      have hjb : ¬ (((Fin.natAdd n b : Fin (n + m)) : ℕ) < n) := by
        simp only [Fin.coe_natAdd]; omega
      rw [blockOne_apply_of_not_lt_of_not_lt M _ _ hia hjb, blockSum_apply_natAdd_natAdd,
        CStarMatrix.one_apply]
      by_cases h : a = b
      · rw [if_pos (by rw [h]), if_pos h]
      · refine (if_neg ?_).trans (if_neg h).symm
        intro hc
        refine h (Fin.eq_of_val_eq ?_)
        have hval := congrArg Fin.val hc
        simp only [Fin.coe_natAdd] at hval
        omega

theorem blockOneUnitary_eq_blockSumU {n m : ℕ} (h : n ≤ n + m)
    (x : unitary (CStarMat n A)) :
    blockOneUnitary h x = blockSumU x (1 : unitary (CStarMat m A)) :=
  Subtype.ext (blockOne_eq_blockSum (x : CStarMat n A) m)

/-! ## The block swap as a unitary -/

variable (A) in
/-- The block swap of `M_{n+n}(A)`, as a unitary.  It is self-adjoint, hence lies in the
identity component of the unitary group. -/
def swapU (n : ℕ) : unitary (CStarMat (n + n) A) :=
  ⟨permMat A (finSumSwap n n), permMat_mem_unitary _⟩

theorem isSelfAdjoint_swapU (n : ℕ) : IsSelfAdjoint ((swapU A n : unitary (CStarMat (n + n) A))
    : CStarMat (n + n) A) :=
  isSelfAdjoint_permMat (finSumSwap_symm_self n)

theorem swapU_conj_blockSumU {n : ℕ} (x y : unitary (CStarMat n A)) :
    swapU A n * blockSumU x y * swapU A n = blockSumU y x := by
  refine Subtype.ext ?_
  have hconj := permMat_conj (A := A) (finSumSwap n n)
    (blockSum (x : CStarMat n A) (y : CStarMat n A))
  rw [finSumSwap_symm_self] at hconj
  show permMat A (finSumSwap n n) * blockSum (x : CStarMat n A) (y : CStarMat n A)
      * permMat A (finSumSwap n n) = blockSum (y : CStarMat n A) (x : CStarMat n A)
  rw [hconj, blockSum_comm]

end Algebra

section Whitehead

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem swapU_mem_unitaryComponentOne (n : ℕ) :
    swapU A n ∈ unitaryComponentOne (CStarMat (n + n) A) :=
  mem_unitaryComponentOne_of_isSelfAdjoint (isSelfAdjoint_swapU n)

theorem unitaryClass_blockSumU_swap {n : ℕ} (x y : unitary (CStarMat n A)) :
    unitaryClass (CStarMat (n + n) A) (blockSumU y x)
      = unitaryClass (CStarMat (n + n) A) (blockSumU x y) := by
  have h₁ : unitaryClass (CStarMat (n + n) A) (swapU A n) = 1 :=
    unitaryClass_eq_one_iff.mpr (swapU_mem_unitaryComponentOne n)
  calc unitaryClass (CStarMat (n + n) A) (blockSumU y x)
      = unitaryClass (CStarMat (n + n) A) (swapU A n * blockSumU x y * swapU A n) := by
        rw [swapU_conj_blockSumU]
    _ = unitaryClass (CStarMat (n + n) A) (swapU A n)
          * unitaryClass (CStarMat (n + n) A) (blockSumU x y)
          * unitaryClass (CStarMat (n + n) A) (swapU A n) := by rw [map_mul, map_mul]
    _ = unitaryClass (CStarMat (n + n) A) (blockSumU x y) := by rw [h₁, one_mul, mul_one]

variable (A) in
/-- **The Whitehead lemma.**  `K_1(A)` is commutative. -/
theorem kOne_mul_comm (a b : KOne A) : a * b = b * a := by
  refine GroupTower.commGroup_of_forall_commute (kOneTower A) ?_ a b
  intro n x y
  refine QuotientGroup.induction_on x fun u => ?_
  refine QuotientGroup.induction_on y fun v => ?_
  have hn : n ≤ n + n := Nat.le_add_right n n
  have key : ∀ w : unitary (CStarMat n A),
      kOneIota A n (unitaryClass (CStarMat n A) w)
        = kOneIota A (n + n) (unitaryClass (CStarMat (n + n) A) (blockSumU w 1)) := by
    intro w
    rw [← kOneIota_kOneMap A hn (unitaryClass (CStarMat n A) w)]
    congr 1
    show unitaryClass (CStarMat (n + n) A) (blockOneUnitary hn w)
      = unitaryClass (CStarMat (n + n) A) (blockSumU w 1)
    rw [blockOneUnitary_eq_blockSumU]
  show kOneIota A n (unitaryClass (CStarMat n A) u * unitaryClass (CStarMat n A) v)
    = kOneIota A n (unitaryClass (CStarMat n A) v * unitaryClass (CStarMat n A) u)
  rw [← map_mul (unitaryClass (CStarMat n A)) u v,
    ← map_mul (unitaryClass (CStarMat n A)) v u, key (u * v), key (v * u)]
  congr 1
  have e₁ : blockSumU u (1 : unitary (CStarMat n A)) * blockSumU v 1 = blockSumU (u * v) 1 := by
    rw [blockSumU_mul, one_mul]
  have e₂ : blockSumU v (1 : unitary (CStarMat n A)) * blockSumU u 1 = blockSumU (v * u) 1 := by
    rw [blockSumU_mul, one_mul]
  have e₃ : blockSumU u (1 : unitary (CStarMat n A)) * blockSumU 1 v = blockSumU u v := by
    rw [blockSumU_mul, mul_one, one_mul]
  have e₄ : blockSumU (1 : unitary (CStarMat n A)) v * blockSumU u 1 = blockSumU u v := by
    rw [blockSumU_mul, one_mul, mul_one]
  have hV : unitaryClass (CStarMat (n + n) A) (blockSumU (1 : unitary (CStarMat n A)) v)
      = unitaryClass (CStarMat (n + n) A) (blockSumU v 1) :=
    unitaryClass_blockSumU_swap v 1
  calc unitaryClass (CStarMat (n + n) A) (blockSumU (u * v) 1)
      = unitaryClass (CStarMat (n + n) A) (blockSumU u 1)
          * unitaryClass (CStarMat (n + n) A) (blockSumU v 1) := by rw [← e₁, map_mul]
    _ = unitaryClass (CStarMat (n + n) A) (blockSumU u 1)
          * unitaryClass (CStarMat (n + n) A) (blockSumU 1 v) := by rw [hV]
    _ = unitaryClass (CStarMat (n + n) A) (blockSumU u v) := by rw [← map_mul, e₃]
    _ = unitaryClass (CStarMat (n + n) A) (blockSumU 1 v)
          * unitaryClass (CStarMat (n + n) A) (blockSumU u 1) := by rw [← map_mul, e₄]
    _ = unitaryClass (CStarMat (n + n) A) (blockSumU v 1)
          * unitaryClass (CStarMat (n + n) A) (blockSumU u 1) := by rw [hV]
    _ = unitaryClass (CStarMat (n + n) A) (blockSumU (v * u) 1) := by rw [← e₂, map_mul]

variable (A) in
/-- `K_1(A)` is an abelian group. -/
instance kOneCommGroup : CommGroup (KOne A) where
  mul_comm := kOne_mul_comm A

end Whitehead

end

end GroupApproximation
