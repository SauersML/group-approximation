import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Level permutations and commutator words

`simple_kazhdan_sofic_group.tex` at origin/main 37551fd93, proof of `cor:lef` and `cor:host`, tex l.336–348:

> On Q_k × ℤ/m_k, with m_k = |Q_k|, let t_k add 1 to the second coordinate, and let f_jk multiply the first coordinate of
> (x,i) from the left by μ_k(γ_j)^i, which is well defined as |Q_k| divides m_k. Then [f_jk, t_k] multiplies the first
> coordinate by μ_k(γ_j). On Q_k × ℤ/m_k × ℤ/4^{k+1} let b_k add 1 to the last coordinate, and let a_k act on the level i by
> f_jk if i = 2^{2j−1} and by t_k if i = 4^j, for j ≤ k, and trivially on the other levels. Then b_k^{−n} a_k b_k^n acts on
> the level i as a_k acts on the level i+n. As distinct pairs of powers of 2 have distinct differences, all below a quarter
> of the modulus, the word w_j = [b^{−2^{2j−1}} a b^{2^{2j−1}}, b^{−4^j} a b^{4^j}] evaluated at (a_k, b_k) acts by
> [f_jk, t_k] on the level 0 and trivially on the other levels, for j ≤ k.

For a finite group `Q` and `g j = μ_k(γ_j)` this file defines `tPerm`, `fPerm`, `aPerm` and `bPerm` and proves each
sentence along the printed route:

* `pow_val_add_one` (the power `x ^ i` is well defined on `ℤ/|Q|`) and `commutator_fPerm_tPerm`;
* `conjPow_aPerm_bPerm`: `b^{−n} a b^n` acts on the level `i` as `a` acts on the level `i + n`;
* `two_pow_sub_two_pow_inj`: distinct pairs of powers of `2` have distinct differences, and `level_difference_zero` uses
  the bound by a quarter of the modulus;
* `word_aPerm_bPerm`: `w_j(a_k, b_k)` is `levelZeroMul (g j)`, which multiplies the first coordinate on the level `0`.

Permutations compose right to left, `(σ * τ) z = σ (τ z)`, and `⁅σ, τ⁆ = σ τ σ⁻¹ τ⁻¹`. The printed power `b^{−n}` is
`(b ^ n)⁻¹`.
-/

namespace GroupApproximation
namespace LevelCommutatorWords

open Equiv
open scoped commutatorElement

section Levels

variable {Y L : Type*}

/-- The permutation of `Y × L` acting on the level `i` by `p i`. -/
def levelwise (p : L → Perm Y) : Perm (Y × L) where
  toFun z := (p z.2 z.1, z.2)
  invFun z := ((p z.2).symm z.1, z.2)
  left_inv z := by simp
  right_inv z := by simp

@[simp] theorem levelwise_apply (p : L → Perm Y) (z : Y × L) :
    levelwise p z = (p z.2 z.1, z.2) := rfl

/-- The commutator of two level permutations acts on each level by the commutator there. -/
theorem levelwise_commutator (p q : L → Perm Y) :
    ⁅levelwise p, levelwise q⁆ = levelwise fun i => ⁅p i, q i⁆ :=
  Equiv.ext fun _ => rfl

variable [AddCommGroup L]

/-- The permutation of `Y × L` adding `c` to the level. -/
def shift (c : L) : Perm (Y × L) where
  toFun z := (z.1, z.2 + c)
  invFun z := (z.1, z.2 - c)
  left_inv z := by simp
  right_inv z := by simp

@[simp] theorem shift_apply (c : L) (z : Y × L) : shift c z = (z.1, z.2 + c) := rfl

theorem shift_mul (c d : L) : (shift c : Perm (Y × L)) * shift d = shift (d + c) :=
  Equiv.ext fun z => Prod.ext rfl (add_assoc z.2 d c)

theorem shift_zero : (shift 0 : Perm (Y × L)) = 1 :=
  Equiv.ext fun z => Prod.ext rfl (add_zero z.2)

theorem shift_pow (c : L) : ∀ n : ℕ, (shift c : Perm (Y × L)) ^ n = shift (n • c)
  | 0 => by rw [pow_zero, zero_nsmul, shift_zero]
  | n + 1 => by rw [pow_succ, shift_pow c n, shift_mul, succ_nsmul, add_comm]

theorem shift_inv (c : L) : (shift c : Perm (Y × L))⁻¹ = shift (-c) :=
  inv_eq_of_mul_eq_one_right (by rw [shift_mul, neg_add_cancel, shift_zero])

/-- Conjugating a level permutation by a shift moves the levels. -/
theorem shift_inv_mul_levelwise_mul_shift (c : L) (p : L → Perm Y) :
    (shift c)⁻¹ * levelwise p * shift c = levelwise fun i => p (i + c) := by
  rw [shift_inv]
  exact Equiv.ext fun z => Prod.ext rfl (add_neg_cancel_right z.2 c)

end Levels

section Words

variable {G H : Type*} [Group G] [Group H]

/-- `b ^ (−n) * a * b ^ n`. -/
def conjPow (a b : G) (n : ℕ) : G :=
  (b ^ n)⁻¹ * a * b ^ n

/-- **The word** `w_j = [b^{−2^{2j−1}} a b^{2^{2j−1}}, b^{−4^j} a b^{4^j}]` (tex l.346). -/
def word (j : ℕ) (a b : G) : G :=
  ⁅conjPow a b (2 ^ (2 * j - 1)), conjPow a b (4 ^ j)⁆

theorem map_word (φ : G →* H) (j : ℕ) (a b : G) : φ (word j a b) = word j (φ a) (φ b) := by
  simp only [word, conjPow, commutatorElement_def, map_mul, map_inv, map_pow]

end Words

/-- **Distinct pairs of powers of `2` have distinct differences** (tex l.344–345). -/
theorem two_pow_sub_two_pow_inj :
    ∀ r s r' s' : ℕ, r < s → r' < s' → 2 ^ s - 2 ^ r = 2 ^ s' - 2 ^ r' → r = r' ∧ s = s'
  | 0, s, 0, s', _, _, h => by
    have h1 : 1 ≤ 2 ^ s := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ s' := Nat.one_le_two_pow
    rw [pow_zero] at h
    have h3 : 2 ^ s = 2 ^ s' := by omega
    refine ⟨rfl, ?_⟩
    rcases Nat.lt_trichotomy s s' with hlt | hst | hgt
    · have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).2 hlt
      omega
    · exact hst
    · have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).2 hgt
      omega
  | 0, s, r' + 1, s', hrs, hrs', h => by
    exfalso
    obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
    obtain ⟨t₀, rfl⟩ : ∃ t₀, s' = t₀ + 1 := ⟨s' - 1, by omega⟩
    have hle : 2 ^ r' ≤ 2 ^ t₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 1 ≤ 2 ^ s₀ := Nat.one_le_two_pow
    rw [pow_zero, pow_succ, pow_succ, pow_succ] at h
    omega
  | r + 1, s, 0, s', hrs, hrs', h => by
    exfalso
    obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
    obtain ⟨t₀, rfl⟩ : ∃ t₀, s' = t₀ + 1 := ⟨s' - 1, by omega⟩
    have hle : 2 ^ r ≤ 2 ^ s₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 1 ≤ 2 ^ t₀ := Nat.one_le_two_pow
    rw [pow_zero, pow_succ, pow_succ, pow_succ] at h
    omega
  | r + 1, s, r' + 1, s', hrs, hrs', h => by
    obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
    obtain ⟨t₀, rfl⟩ : ∃ t₀, s' = t₀ + 1 := ⟨s' - 1, by omega⟩
    have hle : 2 ^ r ≤ 2 ^ s₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hle' : 2 ^ r' ≤ 2 ^ t₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ, pow_succ, pow_succ, pow_succ] at h
    have h' : 2 ^ s₀ - 2 ^ r = 2 ^ t₀ - 2 ^ r' := by omega
    obtain ⟨h1, h2⟩ := two_pow_sub_two_pow_inj r s₀ r' t₀ (by omega) (by omega) h'
    exact ⟨by rw [h1], by rw [h2]⟩

theorem four_pow_eq (j : ℕ) : 4 ^ j = 2 ^ (2 * j) := by
  rw [pow_mul]
  norm_num

section Coordinates

variable (Q : Type*) [Group Q] [Fintype Q]

instance cardNeZero : NeZero (Fintype.card Q) :=
  ⟨Fintype.card_ne_zero⟩

/-- `t_k`: add `1` to the second coordinate of `Q × ℤ/m`, with `m = |Q|` (tex l.336–337). -/
def tPerm : Perm (Q × ZMod (Fintype.card Q)) :=
  shift 1

/-- `f_jk` for `x = μ_k(γ_j)`: multiply the first coordinate of `(y, i)` from the left by `x ^ i` (tex l.337–338). -/
def fPerm (x : Q) : Perm (Q × ZMod (Fintype.card Q)) :=
  levelwise fun i => Equiv.mulLeft (x ^ i.val)

/-- **Well defined as `|Q|` divides `m`** (tex l.338–339): `x ^ i` depends only on `i` modulo `|Q|`. -/
theorem pow_val_add_one (x : Q) (i : ZMod (Fintype.card Q)) : x ^ (i + 1).val = x * x ^ i.val := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, pow_mod_card, pow_add, pow_mod_card, pow_one, ← pow_succ,
    pow_succ']

/-- **`[f_jk, t_k]` multiplies the first coordinate by `μ_k(γ_j)`** (tex l.339–340). -/
theorem commutator_fPerm_tPerm (x : Q) :
    ⁅fPerm Q x, tPerm Q⁆ = levelwise fun _ => Equiv.mulLeft x := by
  rw [commutatorElement_def, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
  refine Equiv.ext fun z => Prod.ext ?_ rfl
  simp only [Perm.mul_apply, fPerm, tPerm, levelwise_apply, shift_apply, Equiv.coe_mulLeft]
  rw [pow_val_add_one, mul_assoc]

end Coordinates

end LevelCommutatorWords
end GroupApproximation
