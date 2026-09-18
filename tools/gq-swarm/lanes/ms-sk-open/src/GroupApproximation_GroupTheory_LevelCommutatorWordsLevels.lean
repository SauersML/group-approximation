import GroupApproximation.GroupTheory.LevelCommutatorWords

/-!
# The levels of `a_k` and the words `w_j` at level `0`

`simple_kazhdan_sofic_group.tex` at origin/main 696c4b602, proof of `cor:lef` and `cor:host`, tex l.340–348:

> On Q_k × ℤ/m_k × ℤ/4^{k+1} let b_k add 1 to the last coordinate, and let a_k act on the level i by f_jk if i = 2^{2j−1}
> and by t_k if i = 4^j, for j ≤ k, and trivially on the other levels. Then b_k^{−n} a_k b_k^n acts on the level i as a_k
> acts on the level i+n. As distinct pairs of powers of 2 have distinct differences, all below a quarter of the modulus,
> the word w_j = [b^{−2^{2j−1}} a b^{2^{2j−1}}, b^{−4^j} a b^{4^j}] evaluated at (a_k, b_k) acts by [f_jk, t_k] on the
> level 0 and trivially on the other levels, for j ≤ k.

The letters sit on the levels `2^r` with `1 ≤ r ≤ 2k`: `f_jk` on `2^{2j−1}` and `t_k` on `2^{2j} = 4^j`. Every such level is
at most `4^k`, a quarter of the modulus `4^{k+1}`. `level_difference_zero` is the printed difference argument: if both
levels `i + 2^{2j−1}` and `i + 4^j` carry letters, then the pair of exponents has the difference of `(2j−1, 2j)`, so it is
that pair and `i = 0`.
-/

namespace GroupApproximation
namespace LevelCommutatorWords

open Equiv
open scoped commutatorElement

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
  · rw [h]; exact h1
  · rw [h]; exact h2
  · rw [h]

/-- The levels `2^r`, `r ≤ 2k`, lie below the modulus `4^{k+1}`. -/
theorem two_pow_lt {r : ℕ} (hr : r ≤ 2 * k) : 2 ^ r < 4 ^ (k + 1) := by
  have h1 : 2 ^ r ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) hr
  have h2 : 4 ^ (k + 1) = 2 ^ (2 * k) * 4 := by rw [pow_succ, pow_mul]; norm_num
  have h3 : 1 ≤ 2 ^ (2 * k) := Nat.one_le_two_pow
  omega

/-- **The difference argument** (tex l.344–348): if the levels `i + 2^{2j−1}` and `i + 4^j` both carry letters, then
`i = 0`. -/
theorem level_difference_zero {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) {i : ZMod (4 ^ (k + 1))}
    (hx : IsLevel k (i + ((2 ^ (2 * j - 1) : ℕ) : ZMod (4 ^ (k + 1)))).val)
    (hy : IsLevel k (i + ((2 ^ (2 * j) : ℕ) : ZMod (4 ^ (k + 1)))).val) : i = 0 := by
  obtain ⟨r, hr1, hr2, hxv⟩ := isLevel_exists hx
  obtain ⟨s, hs1, hs2, hyv⟩ := isLevel_exists hy
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
  have hK : 4 ^ (k + 1) = 2 ^ (2 * k) * 4 := by rw [pow_succ, pow_mul]; norm_num
  have hsK : 2 ^ s ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) hs2
  have hrK : 2 ^ r ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) hr2
  have hpK : 2 ^ (2 * j - 1) ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqK : 2 ^ (2 * j) ≤ 2 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpq : 2 ^ (2 * j) = 2 ^ (2 * j - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hp1 : 1 ≤ 2 ^ (2 * j - 1) := Nat.one_le_two_pow
  have heq : 2 ^ s + 2 ^ (2 * j - 1) = 2 ^ (2 * j) + 2 ^ r := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).1 hmod
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt (show 2 ^ s + 2 ^ (2 * j - 1) < 4 ^ (k + 1) by omega),
      Nat.mod_eq_of_lt (show 2 ^ (2 * j) + 2 ^ r < 4 ^ (k + 1) by omega)] at h
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

/-- The letter on the level `2^r`: `f_jk` with `x = g j` if `r = 2j − 1`, and `t_k` if `r = 2j` (tex l.341–342). -/
def letter (r : ℕ) : Perm (Q × ZMod (Fintype.card Q)) :=
  if Even r then tPerm Q else fPerm Q (g ((r + 1) / 2))

theorem letter_odd {j : ℕ} (hj : 1 ≤ j) : letter Q g (2 * j - 1) = fPerm Q (g j) := by
  have h1 : ¬ Even (2 * j - 1) := by rw [Nat.even_iff]; omega
  have h2 : (2 * j - 1 + 1) / 2 = j := by omega
  rw [letter, if_neg h1, h2]

theorem letter_even (j : ℕ) : letter Q g (2 * j) = tPerm Q := by
  rw [letter, if_pos (even_two_mul j)]

/-- `a_k` on the level `i`: the letter on the levels `2^r`, `1 ≤ r ≤ 2k`, and trivial on the other levels (tex l.341–343). -/
def levelAction (i : ZMod (4 ^ (k + 1))) : Perm (Q × ZMod (Fintype.card Q)) :=
  if IsLevel k i.val then letter Q g (Nat.log 2 i.val) else 1

/-- `a_k` on `Q × ℤ/m × ℤ/4^{k+1}` (tex l.341–343). -/
def aPerm : Perm ((Q × ZMod (Fintype.card Q)) × ZMod (4 ^ (k + 1))) :=
  levelwise (levelAction Q k g)

/-- `b_k`: add `1` to the last coordinate (tex l.340–341). -/
def bPerm : Perm ((Q × ZMod (Fintype.card Q)) × ZMod (4 ^ (k + 1))) :=
  shift 1

/-- The permutation multiplying the first coordinate on the level `0` by `x` and acting trivially elsewhere
(tex l.349–351). -/
def levelZeroMul (x : Q) : Perm ((Q × ZMod (Fintype.card Q)) × ZMod (4 ^ (k + 1))) :=
  levelwise fun i => if i = 0 then levelwise (fun _ => Equiv.mulLeft x) else 1

theorem levelZeroMul_mul (x y : Q) :
    levelZeroMul Q k (x * y) = levelZeroMul Q k x * levelZeroMul Q k y := by
  refine Equiv.ext fun z => ?_
  by_cases hi : z.2 = 0 <;> simp [levelZeroMul, hi, Equiv.coe_mulLeft]

theorem levelZeroMul_one : levelZeroMul Q k 1 = 1 := by
  refine Equiv.ext fun z => ?_
  obtain ⟨y, i⟩ := z
  by_cases hi : i = 0
  · subst hi
    simp [levelZeroMul]
  · simp [levelZeroMul, hi]

theorem eq_one_of_levelZeroMul_eq_one {x : Q} (h : levelZeroMul Q k x = 1) : x = 1 := by
  have h1 := Equiv.congr_fun h ((1, 0), 0)
  simpa [levelZeroMul, Equiv.coe_mulLeft] using congrArg (fun z => z.1.1) h1

theorem levelAction_two_pow {r : ℕ} (h1 : 1 ≤ r) (h2 : r ≤ 2 * k) :
    levelAction Q k g ((2 ^ r : ℕ) : ZMod (4 ^ (k + 1))) = letter Q g r := by
  rw [levelAction, ZMod.val_cast_of_lt (two_pow_lt k h2), if_pos (isLevel_two_pow k h1 h2),
    Nat.log_pow (by norm_num : 1 < 2)]

theorem levelAction_eq_one {i : ZMod (4 ^ (k + 1))} (h : ¬ IsLevel k i.val) :
    levelAction Q k g i = 1 := by
  rw [levelAction, if_neg h]

/-- **`b_k^{−n} a_k b_k^n` acts on the level `i` as `a_k` acts on the level `i + n`** (tex l.343–344). -/
theorem conjPow_aPerm_bPerm (n : ℕ) :
    conjPow (aPerm Q k g) (bPerm Q k) n =
      levelwise fun i => levelAction Q k g (i + (n : ZMod (4 ^ (k + 1)))) := by
  rw [conjPow, bPerm, shift_pow, Nat.smul_one_eq_cast, aPerm, shift_inv_mul_levelwise_mul_shift]

/-- The commutator of the two conjugates on the level `i` (tex l.344–348). -/
theorem levelAction_commutator {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) (i : ZMod (4 ^ (k + 1))) :
    ⁅levelAction Q k g (i + ((2 ^ (2 * j - 1) : ℕ) : ZMod (4 ^ (k + 1)))),
      levelAction Q k g (i + ((2 ^ (2 * j) : ℕ) : ZMod (4 ^ (k + 1))))⁆ =
      if i = 0 then levelwise (fun _ => Equiv.mulLeft (g j)) else 1 := by
  by_cases hi : i = 0
  · rw [if_pos hi, hi, zero_add, zero_add,
      levelAction_two_pow Q k g (r := 2 * j - 1) (by omega) (by omega),
      levelAction_two_pow Q k g (r := 2 * j) (by omega) (by omega), letter_odd Q g hj,
      letter_even Q g j, commutator_fPerm_tPerm]
  · rw [if_neg hi]
    by_cases hx : IsLevel k (i + ((2 ^ (2 * j - 1) : ℕ) : ZMod (4 ^ (k + 1)))).val
    · by_cases hy : IsLevel k (i + ((2 ^ (2 * j) : ℕ) : ZMod (4 ^ (k + 1)))).val
      · exact absurd (level_difference_zero k hj hjk hx hy) hi
      · rw [levelAction_eq_one Q k g hy, commutatorElement_one_right]
    · rw [levelAction_eq_one Q k g hx, commutatorElement_one_left]

/-- **The word `w_j` evaluated at `(a_k, b_k)` acts by `[f_jk, t_k]` on the level `0` and trivially on the other levels,
for `j ≤ k`** (tex l.344–348), in the form `w_j(a_k, b_k) = levelZeroMul (g j)`. -/
theorem word_aPerm_bPerm {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    word j (aPerm Q k g) (bPerm Q k) = levelZeroMul Q k (g j) := by
  rw [word, conjPow_aPerm_bPerm, conjPow_aPerm_bPerm, levelwise_commutator, four_pow_eq j]
  exact congrArg levelwise (funext fun i => levelAction_commutator Q k g hj hjk i)

end Letters

end LevelCommutatorWords
end GroupApproximation
