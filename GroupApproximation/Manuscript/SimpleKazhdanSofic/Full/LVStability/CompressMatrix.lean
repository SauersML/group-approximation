import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSuperperfect.Compression

/-!
# Compression of coordinate `0`: the leaf isomorphism `M_{p+1}(A) ≅ M_p(A)`

Matrix part of the stability step of leaf T1b.iii
(`simple_kazhdan_sofic_group.tex`, l.733-735, `sec:questions`; Khanh, arXiv:2609.08428).

Let `A` carry a binary Leavitt family `s₀, s₁, t₀, t₁`.  Coordinate `0` of `A^{p+1}` is split
by `s₀ t₀ + s₁ t₁ = 1`; its `s₁`-half is merged with the extra coordinate `p`.  Concretely:

* `dL k = s₀`, `dR k = t₀` for `k = 0`, and `dL k = dR k = 1` otherwise;
* `compA p : M_{p × (p+1)}(A)` has entries `dL k` at `(k, k)` and `s₁` at `(0, p)`;
* `compB p : M_{(p+1) × p}(A)` has entries `dR k` at `(k, k)` and `t₁` at `(p, 0)`.

Then `compA * compB = 1` and (for `p > 0`) `compB * compA = 1`, so `X ↦ compA X compB` and
`Y ↦ compB Y compA` are mutually inverse monoid isomorphisms, and
`compA E_{ij}(a) compB = E_{ij}(dL i · a · dR j)` for `i, j < p`.
-/

set_option linter.unusedSimpArgs false

namespace GroupApproximation
namespace Full
namespace LVStability

variable {A : Type*} [Ring A] (F : LeavittFamily A)

section Scalars

/-- Left diagonal entry: `s₀` at coordinate `0`, `1` elsewhere. -/
def dL {p : ℕ} (k : Fin p) : A := if (k : ℕ) = 0 then F.s0 else 1

/-- Right diagonal entry: `t₀` at coordinate `0`, `1` elsewhere. -/
def dR {p : ℕ} (k : Fin p) : A := if (k : ℕ) = 0 then F.t0 else 1

variable {p : ℕ}

theorem dL_of_eq {k : Fin p} (h : (k : ℕ) = 0) : dL F k = F.s0 := by
  rw [dL, if_pos h]

theorem dL_of_ne {k : Fin p} (h : ¬(k : ℕ) = 0) : dL F k = 1 := by
  rw [dL, if_neg h]

theorem dR_of_eq {k : Fin p} (h : (k : ℕ) = 0) : dR F k = F.t0 := by
  rw [dR, if_pos h]

theorem dR_of_ne {k : Fin p} (h : ¬(k : ℕ) = 0) : dR F k = 1 := by
  rw [dR, if_neg h]

theorem dR_mul_dL (k : Fin p) : dR F k * dL F k = 1 := by
  by_cases h : (k : ℕ) = 0
  · rw [dR_of_eq F h, dL_of_eq F h, F.t0_s0]
  · rw [dR_of_ne F h, dL_of_ne F h, mul_one]

theorem dL_castLE {q : ℕ} (h : p ≤ q) (k : Fin p) : dL F (Fin.castLE h k) = dL F k :=
  rfl

theorem dR_castLE {q : ℕ} (h : p ≤ q) (k : Fin p) : dR F (Fin.castLE h k) = dR F k :=
  rfl

/-- `w s₀ = s₀ s₀` for the compression conjugator `w`. -/
theorem compressionConjUnit_val_mul_s0 :
    ((LVSuperperfect.compressionConjUnit F : Aˣ) : A) * F.s0 = F.s0 * F.s0 := by
  rw [LVSuperperfect.compressionConjUnit_val]
  simp only [add_mul, mul_assoc, F.t0_s0, F.t1_s0, mul_one, mul_zero, add_zero]

/-- `t₀ w⁻¹ = t₀ t₀` for the compression conjugator `w`. -/
theorem t0_mul_compressionConjUnit_inv :
    F.t0 * (((LVSuperperfect.compressionConjUnit F)⁻¹ : Aˣ) : A) = F.t0 * F.t0 := by
  show F.t0 * (F.s0 * F.t0 * F.t0 + F.s1 * F.s0 * F.t1 * F.t0 + F.s1 * F.s1 * F.t1) =
    F.t0 * F.t0
  simp only [mul_add, ← mul_assoc, F.t0_s0, F.t0_s1, one_mul, zero_mul, add_zero]

end Scalars

section Matrices

/-- The `p × (p+1)` compression matrix. -/
def compA (p : ℕ) : Matrix (Fin p) (Fin (p + 1)) A := fun k l =>
  Fin.lastCases (motive := fun _ => A) (if (k : ℕ) = 0 then F.s1 else 0)
    (fun i => if k = i then dL F k else 0) l

/-- The `(p+1) × p` expansion matrix. -/
def compB (p : ℕ) : Matrix (Fin (p + 1)) (Fin p) A := fun l k =>
  Fin.lastCases (motive := fun _ => A) (if (k : ℕ) = 0 then F.t1 else 0)
    (fun i => if i = k then dR F k else 0) l

variable {p : ℕ}

theorem compA_castSucc (k i : Fin p) :
    compA F p k (Fin.castSucc i) = if k = i then dL F k else 0 := by
  simp only [compA, Fin.lastCases_castSucc]

theorem compA_last (k : Fin p) :
    compA F p k (Fin.last p) = if (k : ℕ) = 0 then F.s1 else 0 := by
  simp only [compA, Fin.lastCases_last]

theorem compB_castSucc (i k : Fin p) :
    compB F p (Fin.castSucc i) k = if i = k then dR F k else 0 := by
  simp only [compB, Fin.lastCases_castSucc]

theorem compB_last (k : Fin p) :
    compB F p (Fin.last p) k = if (k : ℕ) = 0 then F.t1 else 0 := by
  simp only [compB, Fin.lastCases_last]

theorem compA_mul_compB : compA F p * compB F p = 1 := by
  ext k k'
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc, Finset.sum_eq_single k, compA_castSucc,
    compB_castSucc, compA_last, compB_last, if_pos (rfl : k = k)]
  · by_cases hkk : k = k'
    · subst hkk
      rw [if_pos (rfl : k = k), Matrix.one_apply_eq]
      by_cases h0 : (k : ℕ) = 0
      · rw [if_pos h0, if_pos h0, dL_of_eq F h0, dR_of_eq F h0, F.sum_range]
      · rw [if_neg h0, if_neg h0, dL_of_ne F h0, dR_of_ne F h0, mul_one, zero_mul, add_zero]
    · rw [if_neg hkk, Matrix.one_apply_ne hkk, mul_zero, zero_add]
      by_cases h0 : (k : ℕ) = 0
      · have h0' : ¬(k' : ℕ) = 0 := fun h => hkk (Fin.ext (h0.trans h.symm))
        rw [if_neg h0', mul_zero]
      · rw [if_neg h0, zero_mul]
  · intro i _ hik
    rw [compA_castSucc, if_neg (Ne.symm hik), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem compB_mul_compA (hp : 0 < p) : compB F p * compA F p = 1 := by
  ext l l'
  rw [Matrix.mul_apply]
  induction l using Fin.lastCases with
  | last =>
    induction l' using Fin.lastCases with
    | last =>
      have h0 : ((⟨0, hp⟩ : Fin p) : ℕ) = 0 := rfl
      rw [Finset.sum_eq_single (⟨0, hp⟩ : Fin p), compB_last, compA_last, if_pos h0,
        if_pos h0, F.t1_s1, Matrix.one_apply_eq]
      · intro k _ hk
        rw [compB_last, if_neg (fun h : (k : ℕ) = 0 => hk (Fin.ext h)), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    | cast b =>
      rw [Finset.sum_eq_single b, compB_last, compA_castSucc, if_pos (rfl : b = b),
        Matrix.one_apply_ne (Fin.castSucc_ne_last b).symm]
      · by_cases h0 : (b : ℕ) = 0
        · rw [if_pos h0, dL_of_eq F h0, F.t1_s0]
        · rw [if_neg h0, zero_mul]
      · intro k _ hkb
        rw [compA_castSucc, if_neg hkb, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ b) h
  | cast a =>
    induction l' using Fin.lastCases with
    | last =>
      rw [Finset.sum_eq_single a, compB_castSucc, compA_last, if_pos (rfl : a = a),
        Matrix.one_apply_ne (Fin.castSucc_ne_last a)]
      · by_cases h0 : (a : ℕ) = 0
        · rw [if_pos h0, dR_of_eq F h0, F.t0_s1]
        · rw [if_neg h0, mul_zero]
      · intro k _ hka
        rw [compB_castSucc, if_neg (Ne.symm hka), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ a) h
    | cast b =>
      rw [Finset.sum_eq_single a, compB_castSucc, compA_castSucc, if_pos (rfl : a = a)]
      · by_cases hab : a = b
        · subst hab
          rw [if_pos (rfl : a = a), dR_mul_dL, Matrix.one_apply_eq]
        · rw [if_neg hab, mul_zero,
            Matrix.one_apply_ne (fun h => hab (Fin.castSucc_inj.1 h))]
      · intro k _ hka
        rw [compB_castSucc, if_neg (Ne.symm hka), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ a) h

/-- Compressing an elementary matrix unit. -/
theorem compA_mul_single_mul_compB (i j : Fin p) (a : A) :
    compA F p * Matrix.single (Fin.castSucc i) (Fin.castSucc j) a * compB F p =
      Matrix.single i j (dL F i * a * dR F j) := by
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castSucc j), Matrix.mul_single_apply_same,
    compA_castSucc, compB_castSucc, Matrix.single_apply]
  · by_cases hx : x = i
    · by_cases hy : j = y
      · rw [if_pos hx, if_pos hy, if_pos (And.intro hx.symm hy), hx, hy]
      · rw [if_neg hy, mul_zero, if_neg (fun h : i = x ∧ j = y => hy h.2)]
    · rw [if_neg hx, zero_mul, zero_mul, if_neg (fun h : i = x ∧ j = y => hx h.1.symm)]
  · intro l _ hl
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `X ↦ compA X compB`, a monoid homomorphism `M_{p+1}(A) → M_p(A)`. -/
def compressMatrixHom (hp : 0 < p) :
    Matrix (Fin (p + 1)) (Fin (p + 1)) A →* Matrix (Fin p) (Fin p) A where
  toFun X := compA F p * X * compB F p
  map_one' := by
    show compA F p * 1 * compB F p = 1
    rw [Matrix.mul_one, compA_mul_compB]
  map_mul' X Y := by
    show compA F p * (X * Y) * compB F p =
      compA F p * X * compB F p * (compA F p * Y * compB F p)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (compB F p) (compA F p), compB_mul_compA F hp, Matrix.one_mul]

/-- `Y ↦ compB Y compA`, a monoid homomorphism `M_p(A) → M_{p+1}(A)`. -/
def expandMatrixHom (hp : 0 < p) :
    Matrix (Fin p) (Fin p) A →* Matrix (Fin (p + 1)) (Fin (p + 1)) A where
  toFun Y := compB F p * Y * compA F p
  map_one' := by
    show compB F p * 1 * compA F p = 1
    rw [Matrix.mul_one, compB_mul_compA F hp]
  map_mul' X Y := by
    show compB F p * (X * Y) * compA F p =
      compB F p * X * compA F p * (compB F p * Y * compA F p)
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (compA F p) (compB F p), compA_mul_compB, Matrix.one_mul]

theorem compressMatrixHom_apply (hp : 0 < p) (X : Matrix (Fin (p + 1)) (Fin (p + 1)) A) :
    compressMatrixHom F hp X = compA F p * X * compB F p :=
  rfl

theorem expandMatrixHom_apply (hp : 0 < p) (Y : Matrix (Fin p) (Fin p) A) :
    expandMatrixHom F hp Y = compB F p * Y * compA F p :=
  rfl

theorem expand_compress (hp : 0 < p) (X : Matrix (Fin (p + 1)) (Fin (p + 1)) A) :
    expandMatrixHom F hp (compressMatrixHom F hp X) = X := by
  rw [expandMatrixHom_apply, compressMatrixHom_apply]
  simp only [Matrix.mul_assoc]
  rw [compB_mul_compA F hp, Matrix.mul_one, ← Matrix.mul_assoc, compB_mul_compA F hp,
    Matrix.one_mul]

/-- Compression of an elementary matrix `1 + E_{ij}(a)` with `i, j < p`. -/
theorem compressMatrixHom_one_add_single (hp : 0 < p) (i j : Fin p) (a : A) :
    compressMatrixHom F hp (1 + Matrix.single (Fin.castSucc i) (Fin.castSucc j) a) =
      1 + Matrix.single i j (dL F i * a * dR F j) := by
  rw [compressMatrixHom_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, compA_mul_compB,
    compA_mul_single_mul_compB]

end Matrices

end LVStability
end Full
end GroupApproximation
