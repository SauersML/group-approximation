import GroupApproximation.AlgTop.ChernSeries

/-!
# Evenness of a top Chern class from an even virtual correction

The closing paragraph of Lemma 3 of the STW Problem LIX manuscript
(`research/artifacts/stw59-simple-ah-k1-counterexample-manuscript-2026-09-05.md`)
reads:

> Finally, `c(W) = c(p^*V) c(δ)`.  The bundle `V` is pulled back from `Y`, which
> has dimension `2m < 2r`; hence `c_r(V) = 0`.  Each remaining term in `c_r(W)`
> contains a positive Chern class of `δ`, and is even.

This file proves that inference, and it proves it as pure algebra in
`TotalChern A`: given `c_r(V) = 0` and `2 ∣ c_j(δ)` for every `j > 0`, the top
class `c_r(V · δ)` is even.  Since `TotalChern A` is a group, `δ = W / V` is
always available, so the hypothesis-free form is
`two_dvd_chernClass_of_div`.

It also records the vanishing that the manuscript gets from a dimension count.
For the bundle actually in play, `V = 1³ ⊕ H` with `H = ⨁_j L_j^{⊕ d_j}`, the
vanishing `c_r(V) = 0` for `r > ∑_j d_j` needs **no** dimension argument at all:
the total class of `V` is a product of `∑_j d_j` line classes, so it is a
polynomial of that degree (`chernClass_prod_line_pow_eq_zero_of_lt`).  The
trivial summands `1³` contribute the identity of the group and drop out.

## Main declarations

* `TotalChern.chernClass_prod_line_pow_eq_zero_of_lt` — `c_k(⨁_j L_j^{⊕d_j}) = 0`
  for `k > ∑_j d_j`.
* `TotalChern.chernClass_trivial_mul_prod_line_pow_eq_zero_of_lt` — the same for
  `1ⁿ ⊕ H`, which is the `hV` hypothesis of the mapping-torus parity lemma.
* `TotalChern.two_dvd_chernClass_mul` — the evenness inference.
* `TotalChern.two_dvd_chernClass_of_div` — the same with `δ = W / V` supplied.
-/

namespace GroupApproximation
namespace AlgTop
namespace TotalChern

open Finset (antidiagonal mem_antidiagonal)

noncomputable section

variable {A : Type*} [CommRing A]

/-- `c_k` of a sum of line bundles vanishes above the rank.  For
`H = ⨁_j L_j^{⊕ d_j}` this is `c_k(H) = 0` whenever `k > ∑_j d_j`; no property of
the base and no dimension count is used. -/
theorem chernClass_prod_line_pow_eq_zero_of_lt {ι : Type*} (s : Finset ι) (h : ι → A)
    (d : ι → ℕ) {k : ℕ} (hk : (∑ j ∈ s, d j) < k) :
    (∏ j ∈ s, (line (h j)) ^ (d j)).chernClass k = 0 := by
  refine RankLE.prod (fun j => ?_) s k hk
  simpa using (rankLE_line (h j)).pow (d j)

/-- **`c_k(1ⁿ ⊕ H) = 0` for `k > rank H`, packaged.**  `T` is the total Chern
class of the trivial summands, which is the identity of `TotalChern A`, so it
drops out and the vanishing is the one above.

This is `hV` of the mapping-torus parity lemma, for `V = 1³ ⊕ H` and
`r = (∑_j d_j) + 3`: no dimension count, no property of the base, and no
nilpotence of the `h j`. -/
theorem chernClass_trivial_mul_prod_line_pow_eq_zero_of_lt {ι : Type*} (s : Finset ι)
    (h : ι → A) (d : ι → ℕ) (T : TotalChern A) (hT : T = 1) {k : ℕ}
    (hk : (∑ j ∈ s, d j) < k) :
    (T * ∏ j ∈ s, (line (h j)) ^ (d j)).chernClass k = 0 := by
  rw [hT, one_mul]
  exact chernClass_prod_line_pow_eq_zero_of_lt s h d hk

/-- The same with the trivial summands written as the identity outright. -/
theorem chernClass_one_mul_prod_line_pow_eq_zero_of_lt {ι : Type*} (s : Finset ι)
    (h : ι → A) (d : ι → ℕ) {k : ℕ} (hk : (∑ j ∈ s, d j) < k) :
    (((1 : TotalChern A)) * ∏ j ∈ s, (line (h j)) ^ (d j)).chernClass k = 0 :=
  chernClass_trivial_mul_prod_line_pow_eq_zero_of_lt s h d 1 rfl hk

/-- If the top Chern class of `V` vanishes and every positive Chern class of `δ`
is even, then the top Chern class of `V · δ` is even. -/
theorem two_dvd_chernClass_mul (V δ : TotalChern A) (r : ℕ)
    (hV : V.chernClass r = 0)
    (hδ : ∀ j, 0 < j → (2 : A) ∣ δ.chernClass j) :
    (2 : A) ∣ (V * δ).chernClass r := by
  rw [chernClass_mul]
  refine Finset.dvd_sum fun p hp => ?_
  rw [mem_antidiagonal] at hp
  rcases Nat.eq_zero_or_pos p.2 with hzero | hpos
  · have hfst : p.1 = r := by omega
    rw [hfst, hV, zero_mul]
    exact dvd_zero 2
  · exact (hδ p.2 hpos).mul_left _

/-- **The closing inference of Lemma 3.**  Write `δ = W / V` for the total Chern
class of the virtual difference `[W] - [V]`.  If `c_r(V) = 0` and every positive
Chern class of `δ` is even, then `c_r(W)` is even. -/
theorem two_dvd_chernClass_of_div (W V : TotalChern A) (r : ℕ)
    (hV : V.chernClass r = 0)
    (hδ : ∀ j, 0 < j → (2 : A) ∣ (W / V).chernClass j) :
    (2 : A) ∣ W.chernClass r := by
  have hW : W = V * (W / V) := (mul_div_cancel_virtual W V).symm
  rw [hW]
  exact two_dvd_chernClass_mul V (W / V) r hV hδ

end

end TotalChern
end AlgTop
end GroupApproximation
