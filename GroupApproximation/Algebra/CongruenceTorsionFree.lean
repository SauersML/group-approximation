import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.NoncommRing
import GroupApproximation.Algebra.GroupTorsionFree

/-!
# Minkowski's lemma at level three

The principal congruence subgroup

  `Γ(3) = ker (SL(n, ℤ) → SL(n, ℤ/3))`

is torsion-free.  This is Minkowski's lemma; the proof formalized here is the
elementary graded one, which needs no `p`-adic machinery.

Write an element of the kernel as `1 + M` with every entry of `M` divisible by
three, and record that condition as `LevelDvd k M`: `3 ^ k` divides every entry
of `M`.  The whole argument is one descent step
(`levelDvd_succ`): if `1 + M` has prime order `p` and `M` is divisible at level
`k ≥ 1`, then `M` is divisible at level `k + 1`.  Iterating, `M` is divisible by
every power of three, hence zero.

The descent has two cases, and they need different amounts of the binomial
expansion.

* For `p ≠ 3` the first-order expansion `(1 + M) ^ p = 1 + p • M + R` with `R`
  at level `2 * k` (`exists_expansion`) already does it: the identity forces
  `3 ^ (2 * k)` to divide `p * Mᵢⱼ`, and `3` is coprime to `p`.
* For `p = 3` that is too coarse — at `k = 1` it returns the hypothesis.  The
  exact cube `(1 + M) ^ 3 = 1 + 3 • M + 3 • M² + M³` (`cube_expansion`) is used
  instead: the two correction terms sit at levels `2 * k + 1` and `3 * k`, both
  at least `k + 2`, so `3 ^ (k + 2)` divides `3 * Mᵢⱼ`.

Passing from prime order to arbitrary finite order is the usual reduction
through `Nat.minFac`, carried out inside the subgroup so that the congruence
condition survives (`eq_one_of_pow_eq_one`).

The output for downstream use is
`isPowerTorsionFree_congruenceSubgroupThree`, in the project's
`IsPowerTorsionFree` form, together with the entrywise matrix phrasing
`matrix_eq_one_of_pow_eq_one`.  Nothing here is specific to rank three: the
dimension is an arbitrary finite index type, and `gamma3` names the rank-three
instance that the partner-group lane consumes.
-/

namespace GroupApproximation
namespace CongruenceTorsionFree

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `LevelDvd k A` records that `3 ^ k` divides every entry of the integer
matrix `A`.  Membership in the level-three congruence subgroup is `LevelDvd 1`
applied to `A - 1`, and the proof of Minkowski's lemma is a descent on `k`. -/
def LevelDvd (k : ℕ) (A : Matrix n n ℤ) : Prop :=
  ∀ i j, (3 : ℤ) ^ k ∣ A i j

namespace LevelDvd

omit [Fintype n] [DecidableEq n] in
/-- Divisibility at a level implies divisibility at every lower level. -/
theorem mono {k l : ℕ} {A : Matrix n n ℤ} (hA : LevelDvd l A) (h : k ≤ l) :
    LevelDvd k A := fun i j => dvd_trans (pow_dvd_pow 3 h) (hA i j)

omit [Fintype n] [DecidableEq n] in
/-- The zero matrix sits at every level. -/
theorem zero {k : ℕ} : LevelDvd k (0 : Matrix n n ℤ) := fun i j => by
  rw [Matrix.zero_apply]
  exact dvd_zero _

omit [Fintype n] [DecidableEq n] in
/-- Levels are preserved by addition. -/
theorem add {k : ℕ} {A B : Matrix n n ℤ} (hA : LevelDvd k A) (hB : LevelDvd k B) :
    LevelDvd k (A + B) := fun i j => by
  rw [Matrix.add_apply]
  exact dvd_add (hA i j) (hB i j)

omit [Fintype n] [DecidableEq n] in
/-- Levels are preserved by natural scaling. -/
theorem nsmul {k : ℕ} {A : Matrix n n ℤ} (hA : LevelDvd k A) (c : ℕ) :
    LevelDvd k (c • A) := fun i j => by
  rw [Matrix.smul_apply, nsmul_eq_mul]
  exact dvd_mul_of_dvd_right (hA i j) _

omit [DecidableEq n] in
/-- Levels add under matrix multiplication: an entry of a product is a sum of
products of entries, and each such product carries both levels. -/
theorem mul {a b : ℕ} {A B : Matrix n n ℤ} (hA : LevelDvd a A) (hB : LevelDvd b B) :
    LevelDvd (a + b) (A * B) := fun i j => by
  rw [Matrix.mul_apply, pow_add]
  exact Finset.dvd_sum fun l _ => mul_dvd_mul (hA i l) (hB l j)

end LevelDvd

/-- Every natural number is smaller than the corresponding power of three. -/
private theorem lt_three_pow (m : ℕ) : m < 3 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      have h1 : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
      have h2 : 3 ^ (m + 1) = 3 ^ m * 3 := pow_succ 3 m
      omega

/-- An integer divisible by every power of three is zero. -/
private theorem int_eq_zero_of_forall_pow_dvd {x : ℤ} (h : ∀ k : ℕ, (3 : ℤ) ^ k ∣ x) :
    x = 0 := by
  by_contra hx
  have hne : x.natAbs ≠ 0 := fun hz => hx (Int.natAbs_eq_zero.mp hz)
  have hdvd : 3 ^ x.natAbs ∣ x.natAbs := by
    have hint := Int.natAbs_dvd_natAbs.mpr (h x.natAbs)
    simpa [Int.natAbs_pow] using hint
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd)
    (not_le.mpr (lt_three_pow x.natAbs))

/-- The exact cube of `1 + M`.  The generic first-order expansion is too coarse
at the prime three, and this identity supplies the missing term. -/
private theorem cube_expansion (M : Matrix n n ℤ) :
    (1 + M) ^ 3 = 1 + (3 : ℕ) • M + (3 : ℕ) • (M * M) + M * (M * M) := by
  noncomm_ring

/-- First-order binomial expansion.  Modulo a remainder at twice the level, the
`m`-th power of `1 + M` is `1 + m • M`: every term of the expansion past the
linear one is a product of at least two copies of `M`. -/
theorem exists_expansion {k : ℕ} {M : Matrix n n ℤ} (hM : LevelDvd k M) (m : ℕ) :
    ∃ R : Matrix n n ℤ, LevelDvd (2 * k) R ∧ (1 + M) ^ m = 1 + m • M + R := by
  induction m with
  | zero => exact ⟨0, LevelDvd.zero, by simp⟩
  | succ m ih =>
      obtain ⟨R, hR, hEq⟩ := ih
      refine ⟨m • (M * M) + R + R * M, ?_, ?_⟩
      · exact ((((hM.mul hM).mono (by omega)).nsmul m).add hR).add
          ((hR.mul hM).mono (by omega))
      · rw [pow_succ, hEq, succ_nsmul]
        noncomm_ring

/-- **The descent step.**  If `1 + M` has prime order and `M` is divisible at
level `k ≥ 1`, then `M` is divisible at level `k + 1`. -/
theorem levelDvd_succ {p : ℕ} (hp : p.Prime) {M : Matrix n n ℤ}
    (hpow : (1 + M) ^ p = 1) {k : ℕ} (hM : LevelDvd k M) (hk : 1 ≤ k) :
    LevelDvd (k + 1) M := by
  by_cases hp3 : p = 3
  · have hMM : LevelDvd (2 * k) (M * M) := (hM.mul hM).mono (by omega)
    have hMMM : LevelDvd (3 * k) (M * (M * M)) := (hM.mul (hM.mul hM)).mono (by omega)
    rw [hp3, cube_expansion] at hpow
    intro i j
    have hent := Matrix.ext_iff.mpr hpow i j
    simp only [Matrix.add_apply, Matrix.smul_apply] at hent
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at hent
    have h3 : (3 : ℤ) * M i j = -((3 : ℤ) * (M * M) i j + (M * (M * M)) i j) := by
      linarith
    have hd1 : (3 : ℤ) ^ (k + 2) ∣ (3 : ℤ) * (M * M) i j := by
      refine dvd_trans (pow_dvd_pow 3 (by omega : k + 2 ≤ 2 * k + 1)) ?_
      have hsplit : (3 : ℤ) ^ (2 * k + 1) = 3 * 3 ^ (2 * k) := by ring
      rw [hsplit]
      exact mul_dvd_mul_left 3 (hMM i j)
    have hd2 : (3 : ℤ) ^ (k + 2) ∣ (M * (M * M)) i j :=
      dvd_trans (pow_dvd_pow 3 (by omega : k + 2 ≤ 3 * k)) (hMMM i j)
    have hd3 : (3 : ℤ) * (3 : ℤ) ^ (k + 1) ∣ (3 : ℤ) * M i j := by
      have hcollect : (3 : ℤ) * (3 : ℤ) ^ (k + 1) = (3 : ℤ) ^ (k + 2) := by ring
      rw [hcollect, h3]
      exact dvd_neg.mpr (dvd_add hd1 hd2)
    exact (mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)).mp hd3
  · obtain ⟨R, hR, hEq⟩ := exists_expansion hM p
    rw [hEq] at hpow
    intro i j
    have hent := Matrix.ext_iff.mpr hpow i j
    simp only [Matrix.add_apply, Matrix.smul_apply] at hent
    simp only [nsmul_eq_mul] at hent
    have hlin : (p : ℤ) * M i j = -(R i j) := by linarith
    have hdvd : (3 : ℤ) ^ (2 * k) ∣ (p : ℤ) * M i j := by
      rw [hlin]
      exact dvd_neg.mpr (hR i j)
    have hcop : IsCoprime ((3 : ℤ) ^ (2 * k)) (p : ℤ) := by
      refine IsCoprime.pow_left ?_
      have hnat : Nat.Coprime 3 p :=
        (Nat.coprime_primes Nat.prime_three hp).mpr fun h => hp3 h.symm
      simpa using Nat.isCoprime_iff_coprime.mpr hnat
    exact dvd_trans (pow_dvd_pow 3 (by omega : k + 1 ≤ 2 * k))
      (hcop.dvd_of_dvd_mul_left hdvd)

/-- **Minkowski's lemma, matrix form at a prime exponent.**  If every entry of
`M` is divisible by three and `1 + M` has prime order, then `M = 0`. -/
theorem eq_zero_of_prime_pow_eq_one {p : ℕ} (hp : p.Prime) {M : Matrix n n ℤ}
    (hM : LevelDvd 1 M) (hpow : (1 + M) ^ p = 1) : M = 0 := by
  have key : ∀ k : ℕ, LevelDvd (k + 1) M := by
    intro k
    induction k with
    | zero => exact hM
    | succ k ih => exact levelDvd_succ hp hpow ih (by omega)
  refine Matrix.ext_iff.mp fun i j => ?_
  rw [Matrix.zero_apply]
  exact int_eq_zero_of_forall_pow_dvd fun k => (key k).mono (by omega) i j

/-- The principal congruence subgroup of level three: the kernel of reduction
of `SL(n, ℤ)` modulo three. -/
def congruenceSubgroupThree : Subgroup (Matrix.SpecialLinearGroup n ℤ) :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 3))).ker

/-- Reduction of an integer modulo three, as a divisibility statement. -/
private theorem intCast_eq_zero_iff (x : ℤ) : ((x : ZMod 3) = 0) ↔ (3 : ℤ) ∣ x := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

/-- Membership in the level-three congruence subgroup is the entrywise
congruence `A ≡ 1 mod 3`. -/
theorem mem_congruenceSubgroupThree {A : Matrix.SpecialLinearGroup n ℤ} :
    A ∈ congruenceSubgroupThree ↔ LevelDvd 1 ((A : Matrix n n ℤ) - 1) := by
  constructor
  · intro hA i j
    rw [pow_one, ← intCast_eq_zero_iff]
    have h1 : (Int.castRingHom (ZMod 3)).mapMatrix (A : Matrix n n ℤ) = 1 := by
      have h := MonoidHom.mem_ker.mp hA
      have h' := congrArg (fun B : Matrix.SpecialLinearGroup n (ZMod 3) =>
        (B : Matrix n n (ZMod 3))) h
      simpa [Matrix.SpecialLinearGroup.map_apply_coe] using h'
    have h2 : (Int.castRingHom (ZMod 3)).mapMatrix ((A : Matrix n n ℤ) - 1) = 0 := by
      rw [map_sub, map_one, h1, sub_self]
    have h3 := Matrix.ext_iff.mpr h2 i j
    simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using h3
  · intro hA
    refine MonoidHom.mem_ker.mpr (Subtype.ext ?_)
    have h2 : (Int.castRingHom (ZMod 3)).mapMatrix ((A : Matrix n n ℤ) - 1) = 0 := by
      refine Matrix.ext_iff.mp fun i j => ?_
      have hij := hA i j
      rw [pow_one, ← intCast_eq_zero_iff] at hij
      simpa [RingHom.mapMatrix_apply, Matrix.map_apply] using hij
    rw [map_sub, map_one, sub_eq_zero] at h2
    simpa [Matrix.SpecialLinearGroup.map_apply_coe] using h2

/-- An element of prime order in the level-three congruence subgroup is
trivial. -/
theorem eq_one_of_prime_pow_eq_one {A : Matrix.SpecialLinearGroup n ℤ}
    (hA : A ∈ congruenceSubgroupThree) {p : ℕ} (hp : p.Prime) (hpow : A ^ p = 1) :
    A = 1 := by
  have hM : LevelDvd 1 ((A : Matrix n n ℤ) - 1) := mem_congruenceSubgroupThree.mp hA
  have hsplit : (1 : Matrix n n ℤ) + ((A : Matrix n n ℤ) - 1) = (A : Matrix n n ℤ) := by
    abel
  have hcoe : ((1 : Matrix n n ℤ) + ((A : Matrix n n ℤ) - 1)) ^ p = 1 := by
    rw [hsplit]
    simpa using congrArg (fun B : Matrix.SpecialLinearGroup n ℤ =>
      (B : Matrix n n ℤ)) hpow
  have hzero : (A : Matrix n n ℤ) - 1 = 0 := eq_zero_of_prime_pow_eq_one hp hM hcoe
  exact Subtype.ext (by simpa [sub_eq_zero] using hzero)

/-- **Minkowski's lemma.**  An element of the level-three congruence subgroup
with a trivial positive power is trivial: the reduction to prime order is the
usual one through the smallest prime factor of the order. -/
theorem eq_one_of_pow_eq_one {A : Matrix.SpecialLinearGroup n ℤ}
    (hA : A ∈ congruenceSubgroupThree) {m : ℕ} (hm : 0 < m) (hpow : A ^ m = 1) :
    A = 1 := by
  by_contra hne
  have hfin : IsOfFinOrder A := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hpow⟩
  have hd0 : 0 < orderOf A := orderOf_pos_iff.mpr hfin
  have hd1 : orderOf A ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  have hprime : Nat.Prime (orderOf A).minFac := Nat.minFac_prime hd1
  have hdvd : (orderOf A).minFac ∣ orderOf A := Nat.minFac_dvd _
  have hq0 : 0 < orderOf A / (orderOf A).minFac :=
    Nat.div_pos (Nat.le_of_dvd hd0 hdvd) hprime.pos
  have hqlt : orderOf A / (orderOf A).minFac < orderOf A :=
    Nat.div_lt_self hd0 hprime.one_lt
  have hmem : A ^ (orderOf A / (orderOf A).minFac) ∈ congruenceSubgroupThree :=
    pow_mem hA _
  have hpow' : (A ^ (orderOf A / (orderOf A).minFac)) ^ (orderOf A).minFac = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel hdvd]
    exact pow_orderOf_eq_one A
  have h1 : A ^ (orderOf A / (orderOf A).minFac) = 1 :=
    eq_one_of_prime_pow_eq_one hmem hprime hpow'
  have h2 : orderOf A ∣ orderOf A / (orderOf A).minFac :=
    orderOf_dvd_iff_pow_eq_one.mpr h1
  exact absurd (Nat.le_of_dvd hq0 h2) (not_le.mpr hqlt)

/-- **Minkowski's lemma in the project's torsion-freeness form.**  The
principal congruence subgroup of level three in `SL(n, ℤ)` is torsion-free. -/
theorem isPowerTorsionFree_congruenceSubgroupThree :
    IsPowerTorsionFree ↥(congruenceSubgroupThree (n := n)) := by
  intro g m hm hpow
  refine Subtype.ext ?_
  have hval : ((g : Matrix.SpecialLinearGroup n ℤ)) ^ m = 1 := by
    simpa using congrArg (fun x : congruenceSubgroupThree =>
      (x : Matrix.SpecialLinearGroup n ℤ)) hpow
  simpa using eq_one_of_pow_eq_one g.2 hm hval

/-- Matrix phrasing: an integer matrix of determinant one, congruent to the
identity modulo three, with a trivial positive power, is the identity. -/
theorem matrix_eq_one_of_pow_eq_one {A : Matrix n n ℤ} (hdet : A.det = 1)
    (hcong : ∀ i j, (3 : ℤ) ∣ (A - 1) i j) {m : ℕ} (hm : 0 < m) (hpow : A ^ m = 1) :
    A = 1 := by
  obtain ⟨B, hB⟩ : ∃ B : Matrix.SpecialLinearGroup n ℤ, (B : Matrix n n ℤ) = A :=
    ⟨⟨A, hdet⟩, rfl⟩
  have hmem : B ∈ congruenceSubgroupThree := by
    refine mem_congruenceSubgroupThree.mpr fun i j => ?_
    rw [pow_one, hB]
    exact hcong i j
  have hpow' : B ^ m = 1 := Subtype.ext (by simpa [hB] using hpow)
  simpa [hB] using congrArg (fun C : Matrix.SpecialLinearGroup n ℤ => (C : Matrix n n ℤ))
    (eq_one_of_pow_eq_one hmem hm hpow')

/-- The rank-three principal congruence subgroup `Γ(3) ≤ SL(3, ℤ)`, the partner
group of the torsion-free non-MF programme. -/
abbrev gamma3 : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ) :=
  congruenceSubgroupThree

/-- `Γ(3) ≤ SL(3, ℤ)` is torsion-free. -/
theorem isPowerTorsionFree_gamma3 : IsPowerTorsionFree ↥gamma3 :=
  isPowerTorsionFree_congruenceSubgroupThree

/-- The elementary matrix `1 + 3 E₁₂`, an element of `Γ(3)` other than the
identity.  It is recorded so that torsion-freeness of `Γ(3)` cannot be read
vacuously. -/
def gamma3Witness : Matrix.SpecialLinearGroup (Fin 3) ℤ :=
  ⟨!![1, 3, 0; 0, 1, 0; 0, 0, 1], by decide⟩

/-- The witness lies in `Γ(3)`. -/
theorem gamma3Witness_mem : gamma3Witness ∈ gamma3 := by
  refine mem_congruenceSubgroupThree.mpr fun i j => ?_
  fin_cases i <;> fin_cases j <;> decide

/-- The witness is not the identity. -/
theorem gamma3Witness_ne_one : gamma3Witness ≠ 1 := by
  intro h
  have h01 := Matrix.SpecialLinearGroup.ext_iff gamma3Witness 1 |>.mp h 0 1
  revert h01
  decide

/-- `Γ(3)` is not the trivial subgroup, so `isPowerTorsionFree_gamma3` is a
statement about an infinite group and not about a point. -/
theorem gamma3_ne_bot : gamma3 ≠ ⊥ := by
  intro h
  exact gamma3Witness_ne_one (Subgroup.mem_bot.mp (h ▸ gamma3Witness_mem))

end CongruenceTorsionFree
end GroupApproximation
