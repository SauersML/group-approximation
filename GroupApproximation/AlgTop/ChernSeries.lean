import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Total Chern classes as normalized power series

A *total Chern class* of a complex vector bundle `E → X` is the inhomogeneous
class

```text
c(E) = 1 + c₁(E) + c₂(E) + ⋯ ∈ H^*(X; ℤ),
```

and the two structural facts a consumer ever uses are that it is **normalized**
(`c₀ = 1`) and **multiplicative** (`c(E ⊕ F) = c(E) c(F)`, the Whitney sum
formula).  This file isolates exactly that algebra, with no topology at all.

## The encoding

Fix a commutative ring `A` — downstream this is the cohomology ring of the base.
Introduce a bookkeeping variable `X` recording cohomological degree, and record a
total Chern class as a formal power series

```text
c(E) = ∑_{k} c_k(E) X^k ∈ A⟦X⟧,   constantCoeff (c E) = 1.
```

`TotalChern A` is the type of such series.  Three things then come for free
rather than by fiat:

* **Whitney** is the multiplication of `TotalChern A` (`chernClass_mul` is the
  coefficientwise form).
* **Virtual bundles.** `TotalChern A` is a `CommGroup`: a normalized series is a
  unit of `A⟦X⟧` (`PowerSeries.invOfUnit`), so for a formal difference
  `δ = [W] - [V]` the total class `c(δ) = c(W) / c(V)` is *defined*, and
  `c(W) = c(V) c(δ)` is the group identity `V * (W / V) = W`
  (`mul_div_cancel_self`).  This is the step that makes sense of the manuscript's
  `δ = [W] - [p^*V]`.
* **Rank bounds.** `RankLE c n` says `c_k = 0` for `k > n`.  It is closed under
  products with ranks adding (`RankLE.mul`), and a line class has rank ≤ 1.

## Main declarations

* `TotalChern` — normalized power series over `A`, a `CommGroup`.
* `TotalChern.chernClass` — the `k`-th Chern class.
* `TotalChern.chernClass_mul` — the Whitney sum formula in coefficients.
* `TotalChern.line` — the total class `1 + a X` of a line bundle with `c₁ = a`.
* `TotalChern.RankLE` and `TotalChern.RankLE.mul` — vanishing above the rank.
* `TotalChern.chernClass_mul_top` — the top class of a product of two classes of
  complementary rank is the product of the top classes.
* `TotalChern.chernClass_prod_line_pow_top` — the manuscript's (2.1):
  `c_m(⨁_j L_j^{⊕d_j}) = ∏_j c₁(L_j)^{d_j}` with `m = ∑_j d_j`, and this needs
  **no** nilpotence of the `c₁(L_j)`: the top coefficient of a product is the
  product of the leading coefficients.

## Scope

This file is the algebra only.  It does not construct `c(E)` for a bundle `E`;
that is the cohomological layer, and it is what makes the *hypotheses* of
`RankLE` and `line` true in a given example.
-/

namespace GroupApproximation
namespace AlgTop

open Finset (antidiagonal mem_antidiagonal)
open scoped PowerSeries

noncomputable section

variable {A : Type*} [CommRing A]

/-- A **total Chern class** over a commutative ring `A`: a formal power series
`1 + c₁ X + c₂ X² + ⋯` whose constant coefficient is `1`.  The variable `X` only
records cohomological degree; the coefficients live in `A`. -/
structure TotalChern (A : Type*) [CommRing A] where
  /-- The underlying power series `∑ₖ cₖ Xᵏ`. -/
  series : PowerSeries A
  /-- Normalization: `c₀ = 1`. -/
  constantCoeff_series : PowerSeries.constantCoeff series = 1

namespace TotalChern

theorem ext {c d : TotalChern A} (h : c.series = d.series) : c = d := by
  cases c; cases d; subst h; rfl

instance : One (TotalChern A) :=
  ⟨⟨1, map_one _⟩⟩

instance : Mul (TotalChern A) :=
  ⟨fun c d => ⟨c.series * d.series, by
    rw [map_mul, c.constantCoeff_series, d.constantCoeff_series, one_mul]⟩⟩

instance : Inv (TotalChern A) :=
  ⟨fun c => ⟨PowerSeries.invOfUnit c.series 1, by
    rw [PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]⟩⟩

@[simp] theorem one_series : (1 : TotalChern A).series = 1 := rfl

@[simp] theorem mul_series (c d : TotalChern A) :
    (c * d).series = c.series * d.series := rfl

@[simp] theorem inv_series (c : TotalChern A) :
    c⁻¹.series = PowerSeries.invOfUnit c.series 1 := rfl

instance : CommGroup (TotalChern A) where
  mul_assoc a b c := ext (mul_assoc a.series b.series c.series)
  one_mul a := ext (one_mul a.series)
  mul_one a := ext (mul_one a.series)
  mul_comm a b := ext (mul_comm a.series b.series)
  inv_mul_cancel a := ext <| by
    refine PowerSeries.invOfUnit_mul a.series 1 ?_
    rw [a.constantCoeff_series, Units.val_one]

/-- The `k`-th Chern class carried by a total Chern class. -/
def chernClass (c : TotalChern A) (k : ℕ) : A := PowerSeries.coeff k c.series

@[simp] theorem chernClass_zero (c : TotalChern A) : c.chernClass 0 = 1 := by
  rw [chernClass, PowerSeries.coeff_zero_eq_constantCoeff_apply, c.constantCoeff_series]

theorem eq_of_chernClass_eq {c d : TotalChern A}
    (h : ∀ k, c.chernClass k = d.chernClass k) : c = d :=
  ext (PowerSeries.ext h)

@[simp] theorem chernClass_one (k : ℕ) :
    (1 : TotalChern A).chernClass k = if k = 0 then 1 else 0 := by
  rw [chernClass, one_series, PowerSeries.coeff_one]

/-- The **Whitney sum formula** in coefficients: the total Chern class of a
direct sum is the product of the total Chern classes. -/
theorem chernClass_mul (c d : TotalChern A) (n : ℕ) :
    (c * d).chernClass n = ∑ p ∈ antidiagonal n, c.chernClass p.1 * d.chernClass p.2 := by
  rw [chernClass, mul_series, PowerSeries.coeff_mul]
  rfl

/-- The total Chern class of a line bundle with first Chern class `a`. -/
def line (a : A) : TotalChern A :=
  ⟨1 + PowerSeries.C a * PowerSeries.X, by
    rw [map_add, map_one, map_mul, PowerSeries.constantCoeff_X, mul_zero, add_zero]⟩

@[simp] theorem line_series (a : A) :
    (line a).series = 1 + PowerSeries.C a * PowerSeries.X := rfl

theorem chernClass_line (a : A) (k : ℕ) :
    (line a).chernClass k = if k = 0 then 1 else if k = 1 then a else 0 := by
  rw [chernClass, line_series, map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X]
  rcases k with _ | _ | k
  · simp
  · simp
  · simp

@[simp] theorem chernClass_line_one (a : A) : (line a).chernClass 1 = a := by
  rw [chernClass_line]; simp

/-- `c` has **rank at most `n`**: every Chern class in degree above `n` vanishes.
For an honest rank-`n` bundle this is `c_k(E) = 0` for `k > n`. -/
def RankLE (c : TotalChern A) (n : ℕ) : Prop := ∀ k, n < k → c.chernClass k = 0

theorem RankLE.mono {c : TotalChern A} {m n : ℕ} (h : c.RankLE m) (hmn : m ≤ n) :
    c.RankLE n := fun k hk => h k (lt_of_le_of_lt hmn hk)

theorem rankLE_one : (1 : TotalChern A).RankLE 0 := by
  intro k hk
  rw [chernClass_one, if_neg hk.ne']

theorem rankLE_line (a : A) : (line a).RankLE 1 := by
  intro k hk
  rw [chernClass_line, if_neg (by omega), if_neg (by omega)]

theorem RankLE.mul {c d : TotalChern A} {m n : ℕ} (hc : c.RankLE m) (hd : d.RankLE n) :
    (c * d).RankLE (m + n) := by
  intro k hk
  rw [chernClass_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [mem_antidiagonal] at hp
  rcases lt_or_ge m p.1 with h | h
  · rw [hc p.1 h, zero_mul]
  · rw [hd p.2 (by omega), mul_zero]

theorem RankLE.pow {c : TotalChern A} {m : ℕ} (hc : c.RankLE m) (d : ℕ) :
    (c ^ d).RankLE (d * m) := by
  induction d with
  | zero => simpa using rankLE_one
  | succ d ih =>
      have := ih.mul hc
      rw [pow_succ]
      exact this.mono (by ring_nf; omega)

theorem RankLE.prod {ι : Type*} {s : Finset ι} {c : ι → TotalChern A} {n : ι → ℕ}
    (h : ∀ i ∈ s, (c i).RankLE (n i)) :
    (∏ i ∈ s, c i).RankLE (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using rankLE_one
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The top Chern class of a product of two total Chern classes of complementary
ranks is the product of their top Chern classes. -/
theorem chernClass_mul_top {c d : TotalChern A} {m n : ℕ}
    (hc : c.RankLE m) (hd : d.RankLE n) :
    (c * d).chernClass (m + n) = c.chernClass m * d.chernClass n := by
  rw [chernClass_mul]
  refine Finset.sum_eq_single (m, n) (fun p hp hne => ?_) (fun hp => ?_)
  · rw [mem_antidiagonal] at hp
    rcases lt_or_ge m p.1 with h | h
    · rw [hc p.1 h, zero_mul]
    · have hp2 : n < p.2 := by
        rcases lt_or_eq_of_le h with h' | h'
        · omega
        · exact absurd (Prod.ext h'.symm (by omega)) hne
      rw [hd p.2 hp2, mul_zero]
  · exact absurd (mem_antidiagonal.2 rfl) hp

/-- The top Chern class of the `d`-fold sum of a line bundle: `c_d(L^{⊕d}) = a^d`
where `a = c₁(L)`. -/
theorem chernClass_line_pow (a : A) (d : ℕ) : ((line a) ^ d).chernClass d = a ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hpow : ((line a) ^ d).RankLE d := by
        simpa using (rankLE_line a).pow d
      have := chernClass_mul_top (c := (line a) ^ d) (d := line a) hpow (rankLE_line a)
      rw [pow_succ, this, ih, chernClass_line_one, pow_succ]

/-- The top Chern class of a finite product is the product of the top Chern
classes, once each factor is known to have the stated rank. -/
theorem chernClass_prod_top {ι : Type*} (s : Finset ι) (c : ι → TotalChern A) (n : ι → ℕ)
    (h : ∀ i ∈ s, (c i).RankLE (n i)) :
    (∏ i ∈ s, c i).chernClass (∑ i ∈ s, n i) = ∏ i ∈ s, (c i).chernClass (n i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hmem : ∀ i ∈ s, (c i).RankLE (n i) := fun i hi =>
        h i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha,
        chernClass_mul_top (h a (Finset.mem_insert_self a s)) (RankLE.prod hmem), ih hmem]

/-- **The manuscript's (2.1).**  For `H = ⨁_j L_j^{⊕ d_j}` with `c₁(L_j) = h j`,
the top Chern class in degree `m = ∑_j d_j` is `∏_j (h j)^{d_j}`.

No nilpotence of the `h j` is needed: this is the statement that the top
coefficient of a product of polynomials is the product of the leading
coefficients. -/
theorem chernClass_prod_line_pow_top {ι : Type*} (s : Finset ι) (h : ι → A) (d : ι → ℕ) :
    (∏ j ∈ s, (line (h j)) ^ (d j)).chernClass (∑ j ∈ s, d j) = ∏ j ∈ s, h j ^ d j := by
  have hrank : ∀ j ∈ s, ((line (h j)) ^ (d j)).RankLE (d j) := by
    intro j _
    simpa using (rankLE_line (h j)).pow (d j)
  rw [chernClass_prod_top s _ d hrank]
  exact Finset.prod_congr rfl fun j _ => chernClass_line_pow (h j) (d j)

/-- The **virtual class identity**: writing `δ = W / V` for the total Chern class
of the formal difference `[W] - [V]`, one has `c(W) = c(V) c(δ)`.  This is the
group law, so it holds with no hypotheses whatsoever. -/
theorem mul_div_cancel_self (W V : TotalChern A) : V * (W / V) = W := by
  rw [div_eq_mul_inv, mul_comm W V⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]

/-- The coefficientwise form of `c(W) = c(V) c(W / V)`. -/
theorem chernClass_eq_sum_div (W V : TotalChern A) (n : ℕ) :
    W.chernClass n = ∑ p ∈ antidiagonal n, V.chernClass p.1 * (W / V).chernClass p.2 := by
  conv_lhs => rw [← mul_div_cancel_self W V]
  rw [chernClass_mul]

end TotalChern

end

end AlgTop
end GroupApproximation
