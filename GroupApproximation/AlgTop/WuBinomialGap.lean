import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The odd-binomial gap in the Wu-formula tower induction

The mod-two route to Lemma 3 of the STW LIX manuscript runs an induction up the
tower `Y_i = ∏_(j < i) CP^(2^(j+1))`, killing the `t x`-component of the mod-two
total Chern class degree by degree.  Each step consumes Wu's formula

```text
Sq^(2 i)(c_j) = ∑_(t ≤ i) binom(j - i + t - 1, t) ⬝ c_(i-t) ⬝ c_(j+t)   (mod 2)
```

and needs, at height `k`, **some `i ≥ 1` with `binom(k + 2 - i, i)` odd**.  This
file settles exactly when such an `i` exists.

## The answer, and it is not what one hopes for

Write `n = k + 2`.  Then

```text
binom(n - i, i) is even for every i ≥ 1   ⟺   n = 2^m - 1.
```

That is `sparseChoose_iff`.  Restated at `k`: the step is blocked exactly when
`k + 3` is a power of two, i.e. at

```text
k = 2^m - 3 = 1, 5, 13, 29, 61, 125, 253, …
```

**The blocked heights are infinite, not finite.**  They thin out (they have
density zero) but they never stop, so no amount of case-checking closes them:
the induction needs a supplementary relation at every `k = 2^m - 3`, or a
different packaging.  The first blocked height is `k = 1`, which is the `γ₄` gap
already met and routed around in the `Y = CP²` computation.  The second is
`k = 5`, and it is the first one no finite check reaches.

## Why the answer has this shape

`∑_i binom(n - i, i) x^i` is the Fibonacci polynomial `F_(n+1)(x)`, and over
`𝔽₂` it satisfies `P_(2n+1) = P_n ^ 2` and `P_(2n) = P_n ^ 2 + x P_(n-1) ^ 2`.
The second identity never yields `1`, because the even part `P_n ^ 2` and the
odd part `x P_(n-1) ^ 2` cannot cancel and `P_(n-1)` has constant term `1`; the
first says `P_(2n+1) = 1 ⟺ P_n = 1`.  Unwinding the binary expansion gives
`n = 2^m - 1`.

The proof below does not build the polynomials.  It runs the same two identities
directly on the coefficients, where they are Lucas' theorem at `p = 2`:
`binom(2a+1, 2b) ≡ binom(a, b)`, `binom(2a, 2b+1) ≡ 0`, and so on.  Those four
congruences are `chooseTwo_two_mul_*` below, proved from Pascal's rule by one
simultaneous induction, since Mathlib has Kummer's theorem but not Lucas'.

## Main declarations

* `chooseTwo` -- the mod-two binomial coefficient, and Pascal's rule for it.
* `chooseTwo_two_mul_two_mul`, `chooseTwo_two_mul_two_mul_add_one`,
  `chooseTwo_two_mul_add_one_two_mul`,
  `chooseTwo_two_mul_add_one_two_mul_add_one` -- Lucas at `p = 2`.
* `SparseChoose` -- "`binom(n - i, i)` is even for every `i ≥ 1`".
* `sparseChoose_iff` -- `SparseChoose n ↔ ∃ m, n + 1 = 2 ^ m`.
* `exists_odd_choose_iff` -- the criterion in the shape the tower uses.
* `no_odd_choose_two_pow_sub_three` -- the infinite family of blocked heights.
-/

namespace GroupApproximation
namespace AlgTop
namespace WuBinomial

/-! ## The mod-two binomial coefficient -/

/-- The binomial coefficient reduced mod two.  Working in `ZMod 2` rather than
with `Nat.ModEq` turns Pascal's rule into an equation a `rw` chain can use, and
turns "the two branches cancel" into `CharTwo.add_self_eq_zero`. -/
def chooseTwo (n k : ℕ) : ZMod 2 := (n.choose k : ZMod 2)

@[simp] theorem chooseTwo_zero_right (n : ℕ) : chooseTwo n 0 = 1 := by
  simp [chooseTwo]

theorem chooseTwo_eq_zero_of_lt {n k : ℕ} (h : n < k) : chooseTwo n k = 0 := by
  simp [chooseTwo, Nat.choose_eq_zero_of_lt h]

/-- Pascal's rule, mod two. -/
theorem chooseTwo_succ_succ (n k : ℕ) :
    chooseTwo (n + 1) (k + 1) = chooseTwo n k + chooseTwo n (k + 1) := by
  simp [chooseTwo, Nat.choose_succ_succ']

theorem chooseTwo_eq_zero_iff (n k : ℕ) : chooseTwo n k = 0 ↔ Even (n.choose k) :=
  ZMod.natCast_eq_zero_iff_even

theorem even_choose_of_lt {n k : ℕ} (h : n < k) : Even (n.choose k) := by
  rw [Nat.choose_eq_zero_of_lt h]
  exact ⟨0, rfl⟩

/-! ## Lucas' theorem at `p = 2` -/

/-- The four congruences of Lucas' theorem at `p = 2`, proved together.  Mathlib
has Kummer's theorem (`Nat.Prime.emultiplicity_choose`) but not Lucas', and
Kummer's carry condition is a clumsier input here than Pascal's rule.

The induction is on `a`: the two statements about `2 a` at height `a + 1` follow
from the two about `2 a + 1` at height `a`, and then the two about `2 a + 3`
follow from those. -/
private theorem lucas_two_aux (a : ℕ) :
    (∀ b, chooseTwo (2 * a) (2 * b) = chooseTwo a b) ∧
    (∀ b, chooseTwo (2 * a) (2 * b + 1) = 0) ∧
    (∀ b, chooseTwo (2 * a + 1) (2 * b) = chooseTwo a b) ∧
    (∀ b, chooseTwo (2 * a + 1) (2 * b + 1) = chooseTwo a b) := by
  induction a with
  | zero =>
    refine ⟨fun b => ?_, fun b => ?_, fun b => ?_, fun b => ?_⟩
    · cases b with
      | zero => norm_num
      | succ c =>
        rw [chooseTwo_eq_zero_of_lt (by omega), chooseTwo_eq_zero_of_lt (by omega)]
    · exact chooseTwo_eq_zero_of_lt (by omega)
    · cases b with
      | zero => norm_num
      | succ c =>
        rw [chooseTwo_eq_zero_of_lt (by omega), chooseTwo_eq_zero_of_lt (by omega)]
    · cases b with
      | zero => norm_num [chooseTwo]
      | succ c =>
        rw [chooseTwo_eq_zero_of_lt (by omega), chooseTwo_eq_zero_of_lt (by omega)]
  | succ a ih =>
    obtain ⟨_, _, ih3, ih4⟩ := ih
    have e1 : 2 * (a + 1) = 2 * a + 1 + 1 := by ring
    have H1 : ∀ b, chooseTwo (2 * (a + 1)) (2 * b) = chooseTwo (a + 1) b := by
      intro b
      cases b with
      | zero => simp
      | succ c =>
        have e2 : 2 * (c + 1) = 2 * c + 1 + 1 := by ring
        have e3 : 2 * c + 1 + 1 = 2 * (c + 1) := by ring
        rw [e1, e2, chooseTwo_succ_succ, ih4 c, e3, ih3 (c + 1), ← chooseTwo_succ_succ]
    have H2 : ∀ b, chooseTwo (2 * (a + 1)) (2 * b + 1) = 0 := by
      intro b
      rw [e1, chooseTwo_succ_succ, ih3 b, ih4 b, CharTwo.add_self_eq_zero]
    refine ⟨H1, H2, fun b => ?_, fun b => ?_⟩
    · cases b with
      | zero => simp
      | succ c =>
        have e2 : 2 * (c + 1) = 2 * c + 1 + 1 := by ring
        have e3 : 2 * c + 1 + 1 = 2 * (c + 1) := by ring
        rw [e2, chooseTwo_succ_succ, H2 c, e3, H1 (c + 1), zero_add]
    · rw [chooseTwo_succ_succ, H1 b, H2 b, add_zero]

theorem chooseTwo_two_mul_two_mul (a b : ℕ) :
    chooseTwo (2 * a) (2 * b) = chooseTwo a b := (lucas_two_aux a).1 b

theorem chooseTwo_two_mul_two_mul_add_one (a b : ℕ) :
    chooseTwo (2 * a) (2 * b + 1) = 0 := (lucas_two_aux a).2.1 b

theorem chooseTwo_two_mul_add_one_two_mul (a b : ℕ) :
    chooseTwo (2 * a + 1) (2 * b) = chooseTwo a b := (lucas_two_aux a).2.2.1 b

theorem chooseTwo_two_mul_add_one_two_mul_add_one (a b : ℕ) :
    chooseTwo (2 * a + 1) (2 * b + 1) = chooseTwo a b := (lucas_two_aux a).2.2.2 b

/-! ## The blocked heights -/

/-- `n` is *choose-sparse* when every Fibonacci-diagonal binomial coefficient
`binom(n - i, i)` with `i ≥ 1` is even -- equivalently, when the tower step at
height `k = n - 2` has no usable `i`. -/
def SparseChoose (n : ℕ) : Prop := ∀ i : ℕ, 1 ≤ i → Even ((n - i).choose i)

theorem sparseChoose_zero : SparseChoose 0 := fun i hi => even_choose_of_lt (by omega)

/-- An even `n ≥ 2` is never sparse: `i = 1` already works, since
`binom(n - 1, 1) = n - 1` is odd. -/
theorem not_sparseChoose_two_mul {n : ℕ} (hn : 1 ≤ n) : ¬ SparseChoose (2 * n) := by
  intro h
  have h1 := h 1 le_rfl
  rw [Nat.choose_one_right] at h1
  obtain ⟨t, ht⟩ := h1
  omega

/-- **The halving step.**  `P_(2n+1) = P_n ^ 2` over `𝔽₂`, read off coefficient
by coefficient: the odd-index coefficients of `P_(2n+1)` vanish, and its
`2j`-th coefficient is the `j`-th coefficient of `P_n`. -/
theorem sparseChoose_two_mul_add_one_iff (n : ℕ) :
    SparseChoose (2 * n + 1) ↔ SparseChoose n := by
  constructor
  · intro h j hj
    rcases le_or_gt j n with hjn | hjn
    · have key := h (2 * j) (by omega)
      have e : 2 * n + 1 - 2 * j = 2 * (n - j) + 1 := by omega
      rw [e, ← chooseTwo_eq_zero_iff, chooseTwo_two_mul_add_one_two_mul] at key
      exact (chooseTwo_eq_zero_iff _ _).mp key
    · have e : n - j = 0 := by omega
      rw [e]
      exact even_choose_of_lt (by omega)
  · intro h i hi
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' i
    · -- `i = 2 j`, and `j ≥ 1` because `i ≥ 1`
      subst hj
      have hj1 : 1 ≤ j := by omega
      rcases le_or_gt j n with hjn | hjn
      · have key := h j hj1
        have e : 2 * n + 1 - 2 * j = 2 * (n - j) + 1 := by omega
        rw [e, ← chooseTwo_eq_zero_iff, chooseTwo_two_mul_add_one_two_mul]
        exact (chooseTwo_eq_zero_iff _ _).mpr key
      · exact even_choose_of_lt (by omega)
    · -- `i = 2 j + 1`: these coefficients vanish outright
      subst hj
      rcases le_or_gt j n with hjn | hjn
      · have e : 2 * n + 1 - (2 * j + 1) = 2 * (n - j) := by omega
        rw [e, ← chooseTwo_eq_zero_iff, chooseTwo_two_mul_two_mul_add_one]
      · exact even_choose_of_lt (by omega)

/-- **The blocked heights, exactly.**  `binom(n - i, i)` is even for every
`i ≥ 1` if and only if `n + 1` is a power of two. -/
theorem sparseChoose_iff (n : ℕ) : SparseChoose n ↔ ∃ m : ℕ, n + 1 = 2 ^ m := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' n
    · subst hj
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · refine ⟨fun _ => ⟨0, by norm_num⟩, fun _ i hi => even_choose_of_lt (by omega)⟩
      · refine ⟨fun h => absurd h (not_sparseChoose_two_mul hjpos), ?_⟩
        rintro ⟨m, hm⟩
        exfalso
        cases m with
        | zero => simp at hm; omega
        | succ m' =>
          have e : (2 : ℕ) ^ (m' + 1) = 2 * 2 ^ m' := by ring
          rw [e] at hm
          omega
    · subst hj
      rw [sparseChoose_two_mul_add_one_iff, ih j (by omega)]
      constructor
      · rintro ⟨m, hm⟩
        refine ⟨m + 1, ?_⟩
        have e : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
        rw [e]
        omega
      · rintro ⟨m, hm⟩
        cases m with
        | zero => exfalso; rw [pow_zero] at hm; omega
        | succ m' =>
          refine ⟨m', ?_⟩
          have e : (2 : ℕ) ^ (m' + 1) = 2 * 2 ^ m' := by ring
          rw [e] at hm
          omega

/-! ## The criterion in the shape the tower induction uses -/

/-- **The gap criterion.**  The Wu step at height `k` has a usable `i` exactly
when `k + 3` is *not* a power of two. -/
theorem exists_odd_choose_iff (k : ℕ) :
    (∃ i : ℕ, 1 ≤ i ∧ Odd ((k + 2 - i).choose i)) ↔ ∀ m : ℕ, k + 3 ≠ 2 ^ m := by
  have h := sparseChoose_iff (k + 2)
  constructor
  · rintro ⟨i, hi, hodd⟩ m hm
    have hs : SparseChoose (k + 2) := h.mpr ⟨m, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hodd) (hs i hi)
  · intro hm
    by_contra hcon
    have hs : SparseChoose (k + 2) := by
      intro i hi
      rw [← Nat.not_odd_iff_even]
      intro hodd
      exact hcon ⟨i, hi, hodd⟩
    obtain ⟨m, hmm⟩ := h.mp hs
    exact hm m (by omega)

/-- **The blocked heights are infinite.**  For every `m ≥ 2` the Wu step at
`k = 2^m - 3` has no usable `i` at all: `k = 1, 5, 13, 29, 61, 125, 253, …`.

They have density zero, but they never stop, so no finite case check closes the
tower induction.  Every one of them needs a supplementary relation. -/
theorem no_odd_choose_two_pow_sub_three {m : ℕ} (hm : 2 ≤ m) :
    ∀ i : ℕ, 1 ≤ i → Even ((2 ^ m - 3 + 2 - i).choose i) := by
  have hfour : (4 : ℕ) ≤ 2 ^ m := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hpos : 0 < 2 ^ m := by omega
  have e : 2 ^ m - 3 + 2 = 2 ^ m - 1 := by omega
  rw [e]
  refine (sparseChoose_iff (2 ^ m - 1)).mpr ⟨m, by omega⟩

/-- The first blocked height, `k = 1`: the `γ₄` gap already met in the `CP²`
computation.  Recorded separately because it is the one instance the geometric
argument has so far had to route around by hand. -/
theorem no_odd_choose_one : ∀ i : ℕ, 1 ≤ i → Even ((1 + 2 - i).choose i) :=
  no_odd_choose_two_pow_sub_three (m := 2) le_rfl

end WuBinomial
end AlgTop
end GroupApproximation
