import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Instances.Matrix

/-!
# The block inclusions `M ↦ diag (M, 1)` between matrix algebras over a C-star algebra

The colimit defining topological `K_1` runs along the block inclusions

    M_n(A) → M_m(A),   M ↦ diag (M, 1),   n ≤ m,

which are unital star monoid homomorphisms.  They are *not* algebra maps: they are not additive.
This file defines them entrywise, proves that they are unital, multiplicative, star-preserving,
continuous and functorial in `n ≤ m`, and packages the induced homomorphism of unitary groups.

Everything here is elementary index bookkeeping.  The one step with content is `blockOne_mul`,
where a sum over `Fin m` collapses onto the upper-left block; `sum_eq_sum_castLE` isolates that
collapse.

Note the local trap: `CStarMatrix.one_apply` unfolds to an `if`, so a rewrite chain through
`Matrix.one_apply_eq` cannot fire.  The proofs below use `CStarMatrix.one_apply` directly, with
`ite_mk_eq` to move between an index of `Fin m` and the corresponding index of `Fin n`.
-/

namespace GroupApproximation

universe u

/-- Square matrices of size `n` with entries in `A`, carrying the C-star matrix structure. -/
abbrev CStarMat (n : ℕ) (A : Type u) : Type u := CStarMatrix (Fin n) (Fin n) A

variable {A : Type u} {n m k : ℕ}

/-- A sum over `Fin m` whose terms vanish outside the first `n` indices is a sum over `Fin n`. -/
theorem sum_eq_sum_castLE {B : Type*} [AddCommMonoid B] (h : n ≤ m) (g : Fin m → B)
    (hg : ∀ i : Fin m, ¬ ((i : ℕ) < n) → g i = 0) :
    ∑ i : Fin m, g i = ∑ i : Fin n, g (Fin.castLE h i) := by
  have key : ∑ i ∈ Finset.univ.image (Fin.castLE h), g i = ∑ i : Fin m, g i := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro x _ hx
    refine hg x fun hlt => hx ?_
    exact Finset.mem_image.mpr ⟨⟨(x : ℕ), hlt⟩, Finset.mem_univ _, rfl⟩
  rw [← key, Finset.sum_image]
  intro a _ b _ hab
  exact (Fin.castLEEmb h).injective hab

/-- Moving an `if` on `Fin n` indices to the corresponding `if` on `Fin m` indices. -/
theorem ite_mk_eq {B : Type*} (i j : Fin m) (hi : (i : ℕ) < n) (hj : (j : ℕ) < n) {a b : B} :
    (if (⟨(i : ℕ), hi⟩ : Fin n) = ⟨(j : ℕ), hj⟩ then a else b) = if i = j then a else b := by
  by_cases hij : (i : ℕ) = (j : ℕ)
  · have h₁ : (⟨(i : ℕ), hi⟩ : Fin n) = ⟨(j : ℕ), hj⟩ := Fin.eq_of_val_eq hij
    have h₂ : i = j := Fin.eq_of_val_eq hij
    rw [if_pos h₁, if_pos h₂]
  · have h₁ : ¬ ((⟨(i : ℕ), hi⟩ : Fin n) = ⟨(j : ℕ), hj⟩) := fun hc =>
      hij (congrArg (Fin.val : Fin n → ℕ) hc)
    have h₂ : ¬ (i = j) := fun hc => hij (congrArg (Fin.val : Fin m → ℕ) hc)
    rw [if_neg h₁, if_neg h₂]

section Algebra

variable [CStarAlgebra A]

/-- The block inclusion `diag (M, 1)`: the `m × m` matrix agreeing with the `n × n` matrix `M`
on the upper-left `n × n` corner and equal to the identity elsewhere.  The definition makes
sense for any `m`; every algebraic property below assumes `n ≤ m`. -/
def blockOne (M : CStarMat n A) (m : ℕ) : CStarMat m A := fun i j =>
  if hi : (i : ℕ) < n then
    (if hj : (j : ℕ) < n then M ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩ else 0)
  else
    (if (j : ℕ) < n then 0 else if i = j then 1 else 0)

theorem blockOne_apply (M : CStarMat n A) (i j : Fin m) :
    blockOne M m i j =
      if hi : (i : ℕ) < n then
        (if hj : (j : ℕ) < n then M ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩ else 0)
      else
        (if (j : ℕ) < n then 0 else if i = j then 1 else 0) := rfl

theorem blockOne_apply_of_lt_of_lt (M : CStarMat n A) (i j : Fin m)
    (hi : (i : ℕ) < n) (hj : (j : ℕ) < n) :
    blockOne M m i j = M ⟨(i : ℕ), hi⟩ ⟨(j : ℕ), hj⟩ := by
  rw [blockOne_apply, dif_pos hi, dif_pos hj]

theorem blockOne_apply_of_lt_of_not_lt (M : CStarMat n A) (i j : Fin m)
    (hi : (i : ℕ) < n) (hj : ¬ ((j : ℕ) < n)) : blockOne M m i j = 0 := by
  rw [blockOne_apply, dif_pos hi, dif_neg hj]

theorem blockOne_apply_of_not_lt_of_lt (M : CStarMat n A) (i j : Fin m)
    (hi : ¬ ((i : ℕ) < n)) (hj : (j : ℕ) < n) : blockOne M m i j = 0 := by
  rw [blockOne_apply, dif_neg hi, if_pos hj]

theorem blockOne_apply_of_not_lt_of_not_lt (M : CStarMat n A) (i j : Fin m)
    (hi : ¬ ((i : ℕ) < n)) (hj : ¬ ((j : ℕ) < n)) :
    blockOne M m i j = if i = j then 1 else 0 := by
  rw [blockOne_apply, dif_neg hi, if_neg hj]

theorem blockOne_apply_castLE_right (h : n ≤ m) (M : CStarMat n A) (i : Fin m)
    (hi : (i : ℕ) < n) (l : Fin n) :
    blockOne M m i (Fin.castLE h l) = M ⟨(i : ℕ), hi⟩ l :=
  blockOne_apply_of_lt_of_lt M i (Fin.castLE h l) hi l.isLt

theorem blockOne_apply_castLE_left (h : n ≤ m) (M : CStarMat n A) (j : Fin m)
    (hj : (j : ℕ) < n) (l : Fin n) :
    blockOne M m (Fin.castLE h l) j = M l ⟨(j : ℕ), hj⟩ :=
  blockOne_apply_of_lt_of_lt M (Fin.castLE h l) j l.isLt hj

theorem blockOne_castLE (h : n ≤ m) (M : CStarMat n A) (i j : Fin n) :
    blockOne M m (Fin.castLE h i) (Fin.castLE h j) = M i j :=
  blockOne_apply_of_lt_of_lt M (Fin.castLE h i) (Fin.castLE h j) i.isLt j.isLt

theorem blockOne_self (M : CStarMat n A) : blockOne M n = M := by
  ext i j
  rw [blockOne_apply_of_lt_of_lt M i j i.isLt j.isLt]

theorem blockOne_one (n m : ℕ) : blockOne (1 : CStarMat n A) m = 1 := by
  ext i j
  by_cases hi : (i : ℕ) < n
  · by_cases hj : (j : ℕ) < n
    · rw [blockOne_apply_of_lt_of_lt (1 : CStarMat n A) i j hi hj, CStarMatrix.one_apply,
        CStarMatrix.one_apply, ite_mk_eq i j hi hj]
    · have h₂ : ¬ (i = j) := by rintro rfl; exact hj hi
      rw [blockOne_apply_of_lt_of_not_lt (1 : CStarMat n A) i j hi hj, CStarMatrix.one_apply,
        if_neg h₂]
  · by_cases hj : (j : ℕ) < n
    · have h₂ : ¬ (i = j) := by rintro rfl; exact hi hj
      rw [blockOne_apply_of_not_lt_of_lt (1 : CStarMat n A) i j hi hj, CStarMatrix.one_apply,
        if_neg h₂]
    · rw [blockOne_apply_of_not_lt_of_not_lt (1 : CStarMat n A) i j hi hj, CStarMatrix.one_apply]

theorem blockOne_mul (h : n ≤ m) (M N : CStarMat n A) :
    blockOne (M * N) m = blockOne M m * blockOne N m := by
  ext i j
  rw [CStarMatrix.mul_apply]
  by_cases hi : (i : ℕ) < n
  · by_cases hj : (j : ℕ) < n
    · rw [blockOne_apply_of_lt_of_lt (M * N) i j hi hj, CStarMatrix.mul_apply,
        sum_eq_sum_castLE h (fun l : Fin m => blockOne M m i l * blockOne N m l j)
          (fun l hl => by rw [blockOne_apply_of_lt_of_not_lt M i l hi hl, zero_mul])]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [blockOne_apply_castLE_right h M i hi l, blockOne_apply_castLE_left h N j hj l]
    · rw [blockOne_apply_of_lt_of_not_lt (M * N) i j hi hj]
      refine (Finset.sum_eq_zero fun l _ => ?_).symm
      by_cases hl : (l : ℕ) < n
      · rw [blockOne_apply_of_lt_of_not_lt N l j hl hj, mul_zero]
      · rw [blockOne_apply_of_lt_of_not_lt M i l hi hl, zero_mul]
  · by_cases hj : (j : ℕ) < n
    · rw [blockOne_apply_of_not_lt_of_lt (M * N) i j hi hj]
      refine (Finset.sum_eq_zero fun l _ => ?_).symm
      by_cases hl : (l : ℕ) < n
      · rw [blockOne_apply_of_not_lt_of_lt M i l hi hl, zero_mul]
      · rw [blockOne_apply_of_not_lt_of_lt N l j hl hj, mul_zero]
    · have hsum : (∑ l : Fin m, blockOne M m i l * blockOne N m l j)
          = blockOne M m i i * blockOne N m i j := by
        refine Finset.sum_eq_single i (fun l _ hli => ?_) (fun hc => absurd (Finset.mem_univ i) hc)
        by_cases hl : (l : ℕ) < n
        · rw [blockOne_apply_of_not_lt_of_lt M i l hi hl, zero_mul]
        · rw [blockOne_apply_of_not_lt_of_not_lt M i l hi hl, if_neg (Ne.symm hli), zero_mul]
      rw [blockOne_apply_of_not_lt_of_not_lt (M * N) i j hi hj, hsum,
        blockOne_apply_of_not_lt_of_not_lt M i i hi hi,
        blockOne_apply_of_not_lt_of_not_lt N i j hi hj, if_pos rfl, one_mul]

theorem blockOne_star (M : CStarMat n A) (m : ℕ) :
    blockOne (star M) m = star (blockOne M m) := by
  ext i j
  rw [CStarMatrix.star_apply]
  by_cases hi : (i : ℕ) < n
  · by_cases hj : (j : ℕ) < n
    · rw [blockOne_apply_of_lt_of_lt (star M) i j hi hj,
        blockOne_apply_of_lt_of_lt M j i hj hi, CStarMatrix.star_apply]
    · rw [blockOne_apply_of_lt_of_not_lt (star M) i j hi hj,
        blockOne_apply_of_not_lt_of_lt M j i hj hi, star_zero]
  · by_cases hj : (j : ℕ) < n
    · rw [blockOne_apply_of_not_lt_of_lt (star M) i j hi hj,
        blockOne_apply_of_lt_of_not_lt M j i hj hi, star_zero]
    · rw [blockOne_apply_of_not_lt_of_not_lt (star M) i j hi hj,
        blockOne_apply_of_not_lt_of_not_lt M j i hj hi]
      by_cases hij : i = j
      · rw [if_pos hij, if_pos hij.symm, star_one]
      · rw [if_neg hij, if_neg (Ne.symm hij), star_zero]

theorem blockOne_trans (h : n ≤ m) (M : CStarMat n A) (k : ℕ) :
    blockOne (blockOne M m) k = blockOne M k := by
  ext i j
  by_cases hi : (i : ℕ) < n
  · have him : (i : ℕ) < m := lt_of_lt_of_le hi h
    by_cases hj : (j : ℕ) < n
    · have hjm : (j : ℕ) < m := lt_of_lt_of_le hj h
      rw [blockOne_apply_of_lt_of_lt (blockOne M m) i j him hjm,
        blockOne_apply_of_lt_of_lt M ⟨(i : ℕ), him⟩ ⟨(j : ℕ), hjm⟩ hi hj,
        blockOne_apply_of_lt_of_lt M i j hi hj]
    · rw [blockOne_apply_of_lt_of_not_lt M i j hi hj]
      by_cases hjm : (j : ℕ) < m
      · rw [blockOne_apply_of_lt_of_lt (blockOne M m) i j him hjm,
          blockOne_apply_of_lt_of_not_lt M ⟨(i : ℕ), him⟩ ⟨(j : ℕ), hjm⟩ hi hj]
      · rw [blockOne_apply_of_lt_of_not_lt (blockOne M m) i j him hjm]
  · by_cases hj : (j : ℕ) < n
    · have hjm : (j : ℕ) < m := lt_of_lt_of_le hj h
      rw [blockOne_apply_of_not_lt_of_lt M i j hi hj]
      by_cases him : (i : ℕ) < m
      · rw [blockOne_apply_of_lt_of_lt (blockOne M m) i j him hjm,
          blockOne_apply_of_not_lt_of_lt M ⟨(i : ℕ), him⟩ ⟨(j : ℕ), hjm⟩ hi hj]
      · rw [blockOne_apply_of_not_lt_of_lt (blockOne M m) i j him hjm]
    · rw [blockOne_apply_of_not_lt_of_not_lt M i j hi hj]
      by_cases him : (i : ℕ) < m
      · by_cases hjm : (j : ℕ) < m
        · rw [blockOne_apply_of_lt_of_lt (blockOne M m) i j him hjm,
            blockOne_apply_of_not_lt_of_not_lt M ⟨(i : ℕ), him⟩ ⟨(j : ℕ), hjm⟩ hi hj,
            ite_mk_eq i j him hjm]
        · have h₂ : ¬ (i = j) := by rintro rfl; exact hjm him
          rw [blockOne_apply_of_lt_of_not_lt (blockOne M m) i j him hjm, if_neg h₂]
      · by_cases hjm : (j : ℕ) < m
        · have h₂ : ¬ (i = j) := by rintro rfl; exact him hjm
          rw [blockOne_apply_of_not_lt_of_lt (blockOne M m) i j him hjm, if_neg h₂]
        · rw [blockOne_apply_of_not_lt_of_not_lt (blockOne M m) i j him hjm]

/-- The block inclusion as a unital star monoid homomorphism `M_n(A) →⋆* M_m(A)`. -/
def blockOneHom (h : n ≤ m) : CStarMat n A →⋆* CStarMat m A where
  toFun M := blockOne M m
  map_one' := blockOne_one n m
  map_mul' M N := blockOne_mul h M N
  map_star' M := blockOne_star M m

@[simp] theorem blockOneHom_apply (h : n ≤ m) (M : CStarMat n A) :
    blockOneHom h M = blockOne M m := rfl

/-- The block inclusion of unitary groups, `u ↦ diag (u, 1)`. -/
def blockOneUnitary (h : n ≤ m) : unitary (CStarMat n A) →* unitary (CStarMat m A) :=
  (Unitary.map (blockOneHom h)).toMonoidHom

@[simp] theorem coe_blockOneUnitary (h : n ≤ m) (u : unitary (CStarMat n A)) :
    ((blockOneUnitary h u : unitary (CStarMat m A)) : CStarMat m A)
      = blockOne (u : CStarMat n A) m := rfl

theorem blockOneUnitary_self (h : n ≤ n) (u : unitary (CStarMat n A)) :
    blockOneUnitary h u = u :=
  Subtype.ext (blockOne_self (u : CStarMat n A))

theorem blockOneUnitary_trans (h₁ : n ≤ m) (h₂ : m ≤ k) (u : unitary (CStarMat n A)) :
    blockOneUnitary h₂ (blockOneUnitary h₁ u) = blockOneUnitary (h₁.trans h₂) u :=
  Subtype.ext (blockOne_trans h₁ (u : CStarMat n A) k)

theorem continuous_blockOne (n m : ℕ) :
    Continuous (fun M : CStarMat n A => blockOne M m) := by
  refine continuous_matrix fun i j => ?_
  by_cases hi : (i : ℕ) < n
  · by_cases hj : (j : ℕ) < n
    · exact (continuous_apply_apply (⟨(i : ℕ), hi⟩ : Fin n) (⟨(j : ℕ), hj⟩ : Fin n)).congr
        fun M => (blockOne_apply_of_lt_of_lt M i j hi hj).symm
    · exact continuous_const.congr fun M => (blockOne_apply_of_lt_of_not_lt M i j hi hj).symm
  · by_cases hj : (j : ℕ) < n
    · exact continuous_const.congr fun M => (blockOne_apply_of_not_lt_of_lt M i j hi hj).symm
    · exact continuous_const.congr
        fun M => (blockOne_apply_of_not_lt_of_not_lt M i j hi hj).symm

theorem continuous_blockOneUnitary [PartialOrder A] [StarOrderedRing A] (h : n ≤ m) :
    Continuous (blockOneUnitary (A := A) h) :=
  continuous_induced_rng.mpr ((continuous_blockOne n m).comp continuous_subtype_val)

end Algebra

end GroupApproximation
