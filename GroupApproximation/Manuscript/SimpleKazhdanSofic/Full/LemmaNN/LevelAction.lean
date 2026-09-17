import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LemmaNN.LevelWords
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Module.NatInt
import Mathlib.Tactic.Abel

/-!
# `lem:nn`: the permutations `a_k`, `b_k` and the words `w_j(a_k, b_k)` at level `0`

`simple_kazhdan_sofic_group.tex`, proof of `lem:nn` (l.504–517):

> On Q_k × ℤ/m_k × ℤ/4^{k+1} let b_k add 1 to the last coordinate, and let a_k act on the level i, the set of points with
> last coordinate i, by f_jk if i = 2^{2j−1} and by t_k if i = 4^j, for j ≤ k, and trivially on the other levels. Then
> b_k^{−n} a_k b_k^n acts on the level i as a_k acts on the level i+n. As distinct ordered pairs of distinct powers of 2
> have distinct nonzero differences, all of absolute value below a quarter of the modulus, the two conjugates in
> w_j = [b^{−2^{2j−1}} a b^{2^{2j−1}}, b^{−4^j} a b^{4^j}], evaluated at (a_k, b_k), cannot both act nontrivially on a
> level other than 0. So w_j(a_k, b_k) acts by [f_jk, t_k] on the level 0 and trivially on the other levels, for j ≤ k.

The letters sit on the levels `2^r` with `1 ≤ r ≤ 2k`: `f_jk` on `2^{2j−1}` and `t_k` on `2^{2j} = 4^j`. Every such level is
at most `4^k`, a quarter of the modulus `4^{k+1}`. The map `μ_k` is recorded by `g : ℕ → Q`, `g j = μ_k(γ_j)`.
-/

namespace GroupApproximation.Full.SK09

open Equiv
open scoped commutatorElement

theorem levelwise_apply_mk {Y L : Type*} (p : L → Perm Y) (y : Y) (i : L) :
    levelwise p (y, i) = (p i y, i) := rfl

instance fourPowNeZero (k : ℕ) : NeZero (4 ^ (k + 1)) :=
  ⟨pow_ne_zero _ (by norm_num)⟩

/-- The value `v` is a level `2^r` with `1 ≤ r ≤ 2k`, which carries a letter of `a_k`. -/
abbrev IsLevel (k v : ℕ) : Prop :=
  1 ≤ Nat.log 2 v ∧ Nat.log 2 v ≤ 2 * k ∧ v = 2 ^ Nat.log 2 v

theorem isLevel_exists {k v : ℕ} (h : IsLevel k v) : ∃ r, 1 ≤ r ∧ r ≤ 2 * k ∧ v = 2 ^ r :=
  ⟨Nat.log 2 v, h.1, h.2.1, h.2.2⟩

section Levels

variable (k : ℕ)

theorem isLevel_two_pow {r : ℕ} (h1 : 1 ≤ r) (h2 : r ≤ 2 * k) : IsLevel k (2 ^ r) := by
  have h := Nat.log_pow (by norm_num : 1 < 2) r
  refine ⟨?_, ?_, ?_⟩
  · rw [h]
    exact h1
  · rw [h]
    exact h2
  · rw [h]

theorem four_pow_succ_eq : 4 ^ (k + 1) = 2 ^ (2 * k) * 4 := by
  rw [pow_succ, four_pow_eq]

/-- The levels `2^r`, `r ≤ 2k`, lie below the modulus `4^{k+1}`. -/
theorem two_pow_lt {r : ℕ} (hr : r ≤ 2 * k) : 2 ^ r < 4 ^ (k + 1) := by
  have h1 : 2 ^ r ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) hr
  have h2 : 4 ^ (k + 1) = 2 ^ (2 * k) * 4 := four_pow_succ_eq k
  have h3 : 1 ≤ 2 ^ (2 * k) := Nat.one_le_two_pow
  omega

/-- **The two conjugates in `w_j` cannot both act nontrivially on a level other than `0`** (`lem:nn`,
simple_kazhdan_sofic_group.tex l.510–515): if the levels `i + 2^{2j−1}` and `i + 4^j` both carry letters, then `i = 0`.
The pair of exponents of these levels has the difference of `(2j−1, 2j)`, so it is that pair. -/
theorem level_difference_zero {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) {i : ZMod (4 ^ (k + 1))}
    (hx : IsLevel k (i + ((2 ^ (2 * j - 1) : ℕ) : ZMod (4 ^ (k + 1)))).val)
    (hy : IsLevel k (i + ((2 ^ (2 * j) : ℕ) : ZMod (4 ^ (k + 1)))).val) : i = 0 := by
  obtain ⟨r, -, hr2, hxv⟩ := isLevel_exists hx
  obtain ⟨s, -, hs2, hyv⟩ := isLevel_exists hy
  have hxe : i + ((2 ^ (2 * j - 1) : ℕ) : ZMod (4 ^ (k + 1))) =
      ((2 ^ r : ℕ) : ZMod (4 ^ (k + 1))) := by
    rw [← hxv, ZMod.natCast_zmod_val]
  have hye : i + ((2 ^ (2 * j) : ℕ) : ZMod (4 ^ (k + 1))) =
      ((2 ^ s : ℕ) : ZMod (4 ^ (k + 1))) := by
    rw [← hyv, ZMod.natCast_zmod_val]
  have hmod : ((2 ^ s + 2 ^ (2 * j - 1) : ℕ) : ZMod (4 ^ (k + 1))) =
      ((2 ^ (2 * j) + 2 ^ r : ℕ) : ZMod (4 ^ (k + 1))) := by
    rw [Nat.cast_add, Nat.cast_add, ← hxe, ← hye]
    abel
  have hK : 4 ^ (k + 1) = 2 ^ (2 * k) * 4 := four_pow_succ_eq k
  have hsK : 2 ^ s ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) hs2
  have hrK : 2 ^ r ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) hr2
  have hpK : 2 ^ (2 * j - 1) ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqK : 2 ^ (2 * j) ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpq : 2 ^ (2 * j) = 2 ^ (2 * j - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 * j)]
  have hp1 : 1 ≤ 2 ^ (2 * j - 1) := Nat.one_le_two_pow
  have heq : 2 ^ s + 2 ^ (2 * j - 1) = 2 ^ (2 * j) + 2 ^ r := by
    have h := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hmod
    rw [Nat.mod_eq_of_lt (show 2 ^ s + 2 ^ (2 * j - 1) < 4 ^ (k + 1) by omega),
      Nat.mod_eq_of_lt (show 2 ^ (2 * j) + 2 ^ r < 4 ^ (k + 1) by omega)] at h
    exact h
  have hrs : 2 ^ r < 2 ^ s := by omega
  have hrs' : r < s := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hrs
  have hdiff : 2 ^ s - 2 ^ r = 2 ^ (2 * j) - 2 ^ (2 * j - 1) := by omega
  obtain ⟨hr, -⟩ := two_pow_sub_two_pow_inj r s (2 * j - 1) (2 * j) hrs' (by omega) hdiff
  have hxp : i + ((2 ^ (2 * j - 1) : ℕ) : ZMod (4 ^ (k + 1))) =
      0 + ((2 ^ (2 * j - 1) : ℕ) : ZMod (4 ^ (k + 1))) := by
    rw [hxe, hr, zero_add]
  exact add_right_cancel hxp

end Levels

section Letters

variable (Q : Type*) [Group Q] [Fintype Q] (k : ℕ) (g : ℕ → Q)

/-- The letter on the level `2^r`: `f_jk` with `μ_k(γ_j) = g j` if `r = 2j − 1`, and `t_k` if `r = 2j` (`lem:nn`,
l.506–507). -/
def letter (r : ℕ) : Perm (Q × ZMod (Fintype.card Q)) :=
  if Even r then tPerm Q else fPerm Q (g ((r + 1) / 2))

theorem letter_odd {j : ℕ} (hj : 1 ≤ j) : letter Q g (2 * j - 1) = fPerm Q (g j) := by
  have h1 : ¬ Even (2 * j - 1) := by
    rw [Nat.even_iff]
    omega
  have h2 : (2 * j - 1 + 1) / 2 = j := by omega
  rw [letter, if_neg h1, h2]

theorem letter_even (j : ℕ) : letter Q g (2 * j) = tPerm Q := by
  rw [letter, if_pos (even_two_mul j)]

/-- `a_k` on the level `i`: the letter on the levels `2^r`, `1 ≤ r ≤ 2k`, and trivial on the other levels (`lem:nn`,
l.505–508). -/
def levelAction (i : ZMod (4 ^ (k + 1))) : Perm (Q × ZMod (Fintype.card Q)) :=
  if IsLevel k i.val then letter Q g (Nat.log 2 i.val) else 1

/-- **`a_k`** on `Q_k × ℤ/m_k × ℤ/4^{k+1}` (`lem:nn`, simple_kazhdan_sofic_group.tex l.505–508). -/
def aPerm : Perm ((Q × ZMod (Fintype.card Q)) × ZMod (4 ^ (k + 1))) :=
  levelwise (levelAction Q k g)

/-- **`b_k`**: add `1` to the last coordinate (`lem:nn`, simple_kazhdan_sofic_group.tex l.504–505). -/
def bPerm : Perm ((Q × ZMod (Fintype.card Q)) × ZMod (4 ^ (k + 1))) :=
  shift 1

/-- On the level `i`: `[f_jk, t_k]` (multiplication of the first coordinate by `x`) if `i = 0`, trivial otherwise. -/
def levelZeroLetter (x : Q) (i : ZMod (4 ^ (k + 1))) : Perm (Q × ZMod (Fintype.card Q)) :=
  if i = 0 then levelwise (fun _ => Equiv.mulLeft x) else 1

/-- The permutation multiplying the first coordinate on the level `0` by `x` and acting trivially elsewhere
(`lem:nn`, simple_kazhdan_sofic_group.tex l.518–520). -/
def levelZeroMul (x : Q) : Perm ((Q × ZMod (Fintype.card Q)) × ZMod (4 ^ (k + 1))) :=
  levelwise (levelZeroLetter Q k x)

theorem levelZeroLetter_zero (x : Q) :
    levelZeroLetter Q k x 0 = levelwise (fun _ => Equiv.mulLeft x) := by
  have h : (0 : ZMod (4 ^ (k + 1))) = 0 := rfl
  rw [levelZeroLetter, if_pos h]

theorem levelZeroLetter_mul (x y : Q) (i : ZMod (4 ^ (k + 1))) :
    levelZeroLetter Q k (x * y) i = levelZeroLetter Q k x i * levelZeroLetter Q k y i := by
  by_cases hi : i = 0
  · rw [levelZeroLetter, levelZeroLetter, levelZeroLetter, if_pos hi, if_pos hi, if_pos hi]
    exact Eq.trans (congrArg levelwise (funext fun _ => Equiv.mulLeft_mul x y)) (levelwise_mul _ _).symm
  · rw [levelZeroLetter, levelZeroLetter, levelZeroLetter, if_neg hi, if_neg hi, if_neg hi, mul_one]

theorem levelZeroLetter_one (i : ZMod (4 ^ (k + 1))) : levelZeroLetter Q k 1 i = 1 := by
  by_cases hi : i = 0
  · rw [levelZeroLetter, if_pos hi, Equiv.mulLeft_one, levelwise_one]
  · rw [levelZeroLetter, if_neg hi]

/-- Multiplying on the level `0` is multiplicative (`lem:nn`, l.518–521: the map is a homomorphism). -/
theorem levelZeroMul_mul (x y : Q) :
    levelZeroMul Q k (x * y) = levelZeroMul Q k x * levelZeroMul Q k y :=
  Eq.trans (congrArg levelwise (funext (levelZeroLetter_mul Q k x y))) (levelwise_mul _ _).symm

theorem levelZeroMul_one : levelZeroMul Q k 1 = 1 :=
  Eq.trans (congrArg levelwise (funext (levelZeroLetter_one Q k))) levelwise_one

/-- Multiplying on the level `0` by `x` is trivial only for `x = 1` (`lem:nn`, l.520–521). -/
theorem eq_one_of_levelZeroMul_eq_one {x : Q} (h : levelZeroMul Q k x = 1) : x = 1 := by
  have h1 : levelZeroMul Q k x ((1, 0), 0) = ((1, 0), 0) := Equiv.congr_fun h ((1, 0), 0)
  rw [levelZeroMul, levelwise_apply_mk, levelZeroLetter_zero] at h1
  have h2 : x * 1 = 1 :=
    congrArg (fun z : (Q × ZMod (Fintype.card Q)) × ZMod (4 ^ (k + 1)) => z.1.1) h1
  exact (mul_one x).symm.trans h2

theorem levelAction_two_pow {r : ℕ} (h1 : 1 ≤ r) (h2 : r ≤ 2 * k) :
    levelAction Q k g ((2 ^ r : ℕ) : ZMod (4 ^ (k + 1))) = letter Q g r := by
  rw [levelAction, ZMod.val_natCast_of_lt (two_pow_lt k h2), if_pos (isLevel_two_pow k h1 h2),
    Nat.log_pow (by norm_num : 1 < 2)]

theorem levelAction_eq_one {i : ZMod (4 ^ (k + 1))} (h : ¬ IsLevel k i.val) :
    levelAction Q k g i = 1 := by
  rw [levelAction, if_neg h]

/-- **`b_k^{−n} a_k b_k^n` acts on the level `i` as `a_k` acts on the level `i + n`** (`lem:nn`,
simple_kazhdan_sofic_group.tex l.509–510). -/
theorem conjPow_aPerm_bPerm (n : ℕ) :
    conjPow (aPerm Q k g) (bPerm Q k) n =
      levelwise fun i => levelAction Q k g (i + (n : ZMod (4 ^ (k + 1)))) := by
  rw [conjPow, bPerm, shift_pow, Nat.smul_one_eq_cast, aPerm, shift_inv_mul_levelwise_mul_shift]

/-- The commutator of the two conjugates on the level `i` (`lem:nn`, l.510–517). -/
theorem levelAction_commutator {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (i : ZMod (4 ^ (k + 1))) :
    ⁅levelAction Q k g (i + ((2 ^ (2 * j - 1) : ℕ) : ZMod (4 ^ (k + 1)))),
      levelAction Q k g (i + ((2 ^ (2 * j) : ℕ) : ZMod (4 ^ (k + 1))))⁆ = levelZeroLetter Q k (g j) i := by
  by_cases hi : i = 0
  · rw [hi, levelZeroLetter_zero, zero_add, zero_add,
      levelAction_two_pow Q k g (r := 2 * j - 1) (by omega) (by omega),
      levelAction_two_pow Q k g (r := 2 * j) (by omega) (by omega), letter_odd Q g hj,
      letter_even Q g j, commutator_fPerm_tPerm]
  · rw [levelZeroLetter, if_neg hi]
    by_cases hx : IsLevel k (i + ((2 ^ (2 * j - 1) : ℕ) : ZMod (4 ^ (k + 1)))).val
    · by_cases hy : IsLevel k (i + ((2 ^ (2 * j) : ℕ) : ZMod (4 ^ (k + 1)))).val
      · exact absurd (level_difference_zero k hj hjk hx hy) hi
      · rw [levelAction_eq_one Q k g hy, commutatorElement_one_right]
    · rw [levelAction_eq_one Q k g hx, commutatorElement_one_left]

/-- **`w_j(a_k, b_k)` acts by `[f_jk, t_k]` on the level `0` and trivially on the other levels, for `j ≤ k`** (`lem:nn`,
simple_kazhdan_sofic_group.tex l.516–517), i.e. `w_j(a_k, b_k)` multiplies the first coordinate on the level `0` by
`μ_k(γ_j) = g j`. -/
theorem word_aPerm_bPerm {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    word j (aPerm Q k g) (bPerm Q k) = levelZeroMul Q k (g j) := by
  rw [word, conjPow_aPerm_bPerm, conjPow_aPerm_bPerm, levelwise_commutator, four_pow_eq j]
  exact congrArg levelwise (funext fun i => levelAction_commutator Q k g hj hjk i)

end Letters

end GroupApproximation.Full.SK09
