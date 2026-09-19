import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The parity core of Lemma 3 of the STW LIX manuscript

Lemma 3 of
`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`
says that for any complex rank-`r` bundle `W` over `S^1 × M` restricting to
`V = 1^3 ⊕ H` on the slice `{1} × M`, the top Chern number
`⟨c_r(W), [S^1 × M]⟩` is even.  The Chern-theoretic scaffolding it stands on --
the `TotalChern` group, Newton's identity, the Whitney step -- belongs to
`found-chern-classes`.  What is left, and what this file contains, is the parity
itself, stated for bare sequences `c p : ℕ → S` in a commutative ring so that it
depends on nothing but Mathlib.

`GroupApproximation.AlgTop.MappingTorusParity` (the module without `Core`)
instantiates all of this against `TotalChern`.

## The two simplifications

**No multinomial expansion.**  The manuscript proves the parity by expanding
`ch(β) = exp(∑_j a_j h_j)`, reading the coefficient of `z ∏_j h_j^(b_j)` off as
`(|b|+2)! / ∏_j b_j !`, and observing that this is even.  That route needs the
line-monomial basis of `K^0(Y)`, a multinomial expansion, and an extension by
linearity in `β`.  None of it is needed.  The degree shift is forced -- `z = t x`
sits in degree six, so `ch_q(δ) = 0` for `q < 3` -- and the surviving factorial
quotient is

```text
(q-1)! / (q-3)! = (q-1)(q-2),
```

already a product of two consecutive integers, whatever `ch` happens to be.
That is `chern_factorial_shift`; `two_dvd_of_clearedNewton` is the cleared form
the assembly actually uses.

**No rational cohomology ring.**  Newton's identity in the cleared form
`q ⬝ c_q = (-1)^(q+1) p_q` is valid in any commutative ring.  So the
manuscript's "compute over `ℚ`, return to `ℤ` by torsion-freeness" collapses:
torsion-freeness is used directly, as the cancellation of the integer `q`, and
that is the only thing it is used for.  `H^*(X; ℚ)` and the coefficient map are
never needed.  For a supplier who nevertheless prefers to state the
normalisation with the rational Chern character, `powerSum_eq_of_chernChar` is
the bridge, and it uses nothing about the coefficient map except injectivity --
torsion-freeness again, in its other guise.

## Main declarations

* `even_add_two_mul_add_one` -- `(n+2)(n+1)` is even.
* `chern_factorial_shift` -- the manuscript's (2.7) at the shifted index.
* `two_dvd_of_clearedNewton` -- every positive Chern class of `δ` is even.
* `powerSum_eq_of_chernChar` -- the rational normalisation implies the integral
  hypothesis of `two_dvd_of_clearedNewton`.
* `even_map_of_two_dvd` -- pairing with the fundamental class.
-/

namespace GroupApproximation
namespace AlgTop
namespace MappingTorusParity

open scoped Nat

/-! ## The parity coefficient -/

/-- Two consecutive integers, one of which is even, in the order the degree
shift produces them. -/
theorem even_add_two_mul_add_one (n : ℕ) : Even ((n + 2) * (n + 1)) := by
  have h := Nat.even_mul_succ_self (n + 1)
  rw [Nat.mul_comm] at h
  exact h

/-- **The parity coefficient, with no expansion.**  Substituting `k = n + 3`
into the square-zero Newton conclusion `c_k = (-1)^(k+1) (k-1)! ch_k` and
factoring `(n+2)! = (n+2)(n+1) n !` puts the whole degree shift into a single
product of two consecutive integers, multiplying `n ! ⬝ ch_(n+3)` -- which is an
integral class.

This is the step that makes the manuscript's multinomial expansion of (2.8)
unnecessary: the factorial quotient `(k-1)!/(k-3)!` is already the even
coefficient, whatever `ch` is, so no line-monomial basis of `K^0(Y)` and no
extension by linearity in `β` is required.  The assembly uses the equivalent
cleared form `two_dvd_of_clearedNewton`; this statement is the manuscript's own
display, and takes the conclusion of `chernClass_eq_of_chernChar_sq_zero` as its
hypothesis. -/
theorem chern_factorial_shift {A : Type*} [CommRing A] {c ch : ℕ → A}
    (h : ∀ k : ℕ, 0 < k → c k = (-1 : A) ^ (k + 1) * (((k - 1)! : A) * ch k))
    (n : ℕ) :
    c (n + 3)
      = (-1 : A) ^ n * (((n + 2) * (n + 1) : ℕ) : A) * ((n ! : A) * ch (n + 3)) := by
  have hk := h (n + 3) (by omega)
  have hidx : n + 3 - 1 = n + 2 := by omega
  rw [hidx] at hk
  have hsign : (-1 : A) ^ (n + 3 + 1) = (-1 : A) ^ n := by
    have hn4 : n + 3 + 1 = n + 4 := by omega
    have h4 : (-1 : A) ^ 4 = 1 := by norm_num
    rw [hn4, pow_add, h4, mul_one]
  have hfac : ((n + 2)! : A) = (((n + 2) * (n + 1) : ℕ) : A) * (n ! : A) := by
    have h1 : (n + 2)! = ((n + 2) * (n + 1)) * n ! := by
      have e1 : (n + 2)! = (n + 2) * (n + 1)! := Nat.factorial_succ (n + 1)
      have e2 : (n + 1)! = (n + 1) * n ! := Nat.factorial_succ n
      rw [e1, e2]; ring
    rw [h1, Nat.cast_mul]
  rw [hk, hsign, hfac]
  ring

/-! ## Every positive Chern class of the virtual difference is even -/

/-- **The parity of `δ`.**  Let `c` be the Chern classes of a virtual class and
`p` its power sums, linked by Newton's identity in the cleared form
`q ⬝ c_q = (-1)^(q+1) p_q` -- which is what the square-zero hypothesis
`ch_i ch_j = 0` reduces the full recursion to.  If

* the coefficient ring is torsion free (`htf`),
* `p_q = 0` for `0 < q < 3` (the class `z = t x` sits in degree six), and
* `p_(n+3)` is `(n+3)(n+2)(n+1)` times an integral class -- equivalently, since
  `p_q = q ! ch_q`, the class `n ! ⬝ ch_(n+3)` is integral,

then every positive `c_q` is divisible by two.

Torsion-freeness is used exactly once, to cancel the integer `q` that Newton's
identity leaves in front of `c_q`.  That single cancellation is the whole of the
manuscript's passage from a rational computation to an integral conclusion. -/
theorem two_dvd_of_clearedNewton {S : Type*} [CommRing S]
    (htf : ∀ m : ℕ, m ≠ 0 → ∀ x y : S, (m : S) * x = (m : S) * y → x = y)
    {c p : ℕ → S}
    (hnewton : ∀ q : ℕ, 0 < q → (q : S) * c q = (-1 : S) ^ (q + 1) * p q)
    (hlow : ∀ q : ℕ, 0 < q → q < 3 → p q = 0)
    (hint : ∀ n : ℕ, ∃ w : S,
      p (n + 3) = (((n + 3) * ((n + 2) * (n + 1)) : ℕ) : S) * w) :
    ∀ q : ℕ, 0 < q → (2 : S) ∣ c q := by
  intro q hq
  have hnew := hnewton q hq
  rcases Nat.lt_or_ge q 3 with hq3 | hq3
  · have hcancel : ((q : ℕ) : S) * c q = ((q : ℕ) : S) * 0 := by
      rw [mul_zero, hnew, hlow q hq hq3, mul_zero]
    rw [htf q (by omega) _ _ hcancel]
    exact dvd_zero 2
  · obtain ⟨n, rfl⟩ : ∃ n, q = n + 3 := ⟨q - 3, by omega⟩
    obtain ⟨w, hw⟩ := hint n
    obtain ⟨k, hk⟩ := even_add_two_mul_add_one n
    have hsign : (-1 : S) ^ (n + 3 + 1) = (-1 : S) ^ n := by
      have hn4 : n + 3 + 1 = n + 4 := by omega
      have h4 : (-1 : S) ^ 4 = 1 := by norm_num
      rw [hn4, pow_add, h4, mul_one]
    have hval : c (n + 3) = (-1 : S) ^ n * (((n + 2) * (n + 1) : ℕ) : S) * w := by
      refine htf (n + 3) (by omega) _ _ ?_
      rw [hnew, hw, hsign]
      push_cast
      ring
    rw [hval, hk]
    refine even_iff_two_dvd.mp ⟨(-1 : S) ^ n * (k : S) * w, ?_⟩
    push_cast
    ring

/-- The bridge from the manuscript's rational normalisation of `ch(δ)` to the
integral hypothesis `hint` of `two_dvd_of_clearedNewton`.

A supplier who has `n ! ⬝ ch_(n+3)(δ) = z g^n` in rational cohomology, together
with the coefficient inclusion `ι` and the identification `p_q = q ! ch_q`, gets
`hint` from this and nothing else.  Only injectivity of `ι` is used. -/
theorem powerSum_eq_of_chernChar {S R : Type*} [CommRing S] [CommRing R]
    (ι : S →+* R) (hι : Function.Injective ι)
    {p : ℕ → S} {ch : ℕ → R} {w : ℕ → S}
    (hp : ∀ q : ℕ, ι (p q) = (q ! : R) * ch q)
    (hw : ∀ n : ℕ, ι (w n) = (n ! : R) * ch (n + 3)) (n : ℕ) :
    p (n + 3) = (((n + 3) * ((n + 2) * (n + 1)) : ℕ) : S) * w n := by
  refine hι ?_
  have hfac : ((n + 3)! : ℕ) = ((n + 3) * ((n + 2) * (n + 1))) * n ! := by
    have e1 : (n + 3)! = (n + 3) * (n + 2)! := Nat.factorial_succ (n + 2)
    have e2 : (n + 2)! = (n + 2) * (n + 1)! := Nat.factorial_succ (n + 1)
    have e3 : (n + 1)! = (n + 1) * n ! := Nat.factorial_succ n
    rw [e1, e2, e3]; ring
  rw [map_mul, map_natCast, hp (n + 3), hw n, hfac]
  push_cast
  ring

/-- Divisibility by two survives any additive map.  Applied to evaluation
against the fundamental class this is the last line of Lemma 3: it turns
`(2 : S) ∣ c_r(W)` into the manuscript's `⟨c_r(W), [S^1 × M]⟩ ∈ 2ℤ`. -/
theorem even_map_of_two_dvd {S A : Type*} [CommRing S] [AddCommGroup A]
    (φ : S →+ A) {x : S} (h : (2 : S) ∣ x) : Even (φ x) := by
  obtain ⟨y, rfl⟩ := h
  exact ⟨φ y, by rw [two_mul, map_add]⟩

end MappingTorusParity
end AlgTop
end GroupApproximation
