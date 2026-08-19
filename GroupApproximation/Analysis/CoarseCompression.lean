import GroupApproximation.Algebra.WordMetricBall
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Compression of a large-scale Lipschitz map, and the Gaussian row estimate

This module carries the *quantitative geometric* half of Guentner--Kaminker's
theorem, `E. Guentner and J. Kaminker, Exactness and uniform embeddability of
discrete groups, J. London Math. Soc. (2) 70 (2004), 703--718` (arXiv
`math/0309166`).  Their §2 defines, for a large-scale Lipschitz map
`f : X → Y` of metric spaces, the *compression*

```
    ρ_f(r) = inf { d(f x, f y) : d(x,y) ≥ r }
```

and the *asymptotic compression* `R_f = liminf log ρ*_f(r) / log r`; the
*Hilbert space compression* `R(X)` is the supremum of `R_f` over large-scale
Lipschitz maps into Hilbert space.  Their Theorem 3.2 is

> **if `R(Γ) > 1/2` then `Γ` is exact**,

and the single place where the threshold `1/2` is used is the estimate (14) in
the proof of their Lemma 3.5.  That estimate is what this file proves.

## Where `1/2` comes from, exactly

`R(Γ) > 1/2` supplies a large-scale Lipschitz `f` and an `ε > 0` with
`ρ_f(r) ≥ r^{(1+ε)/2}` for large `r` --- so `‖f s - f t‖² ≥ d(s,t)^{1+ε}` and
the Gaussian kernel obeys

```
    exp(-κ‖f s - f t‖²)  ≤  exp(-κ · d(s,t)^{1+ε}) .
```

A word metric has at most exponential growth: the sphere of radius `n` has at
most `Λⁿ` points (`WordMetric.card_le_pow_of_wordDist_le`).  So the row sum of
the kernel is dominated by

```
    Σ_n  Λⁿ · exp(-κ n^{1+ε}) ,
```

and this converges **exactly because the exponent `1 + ε` exceeds `1`**: for
`n ≥ m` one has `n^{1+ε} ≥ n·m^ε`, so the `n`-th term is at most
`(Λ · exp(-κ m^ε))ⁿ`, a geometric series with ratio `< 1` once `m` is large.
Exponent `1` --- that is, compression exponent exactly `1/2` --- would leave a
ratio `Λ · exp(-κ)`, which is not `< 1` for small `κ`, and the argument stops.
That is the whole role of the hypothesis `R(Γ) > 1/2`; it is not a convenience.

## Statements

* `IsLargeScaleLipschitz`, `HasCompressionExponent` --- the two clauses of
  Guentner--Kaminker (2) and (12);
* `gaussianKernel` --- their `u_k`, with `κ = 1/k`;
* `exists_tail_bound` --- **the estimate (14)**: beyond a radius depending only
  on the tolerance, the tail of every Gaussian row is uniformly small;
* `exists_schur_bound` --- the Schur test input: all rows are bounded by one
  constant, uniformly in the base point.

Nothing here is conditional: the two clauses are hypotheses on `f` and the
conclusions are proved outright.
-/

namespace GroupApproximation
namespace CoarseCompression

open scoped BigOperators

universe u v

variable {G : Type u} [Group G] {E : Type v} [NormedAddCommGroup E]

/-! ## The two clauses on the map -/

/-- **Large-scale Lipschitz**, Guentner--Kaminker (2): `d(f x, f y) ≤ C d(x,y) + D`.
The word metric is the one attached to the alphabet `S`. -/
def IsLargeScaleLipschitz (S : Set G) (f : G → E) : Prop :=
  ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
    ∀ x y : G, ‖f x - f y‖ ≤ C * (WordMetric.wordDist S x y : ℝ) + D

/-- **Compression at exponent `β`**, Guentner--Kaminker (12): beyond a radius
`r₀` the map does not compress distances below their `β`-th power.

This is the working form of `ρ_f(r) ≥ r^β for r ≥ r₀`: since `ρ_f` is an
infimum over pairs at distance at least `r`, the displayed inequality for all
pairs at distance at least `r₀` is exactly that statement. -/
def HasCompressionExponent (S : Set G) (f : G → E) (β : ℝ) : Prop :=
  ∃ r₀ : ℕ, ∀ x y : G, r₀ ≤ WordMetric.wordDist S x y →
    ((WordMetric.wordDist S x y : ℝ)) ^ β ≤ ‖f x - f y‖

/-- **Hilbert space compression exceeding `β₀`** in the sense of
Guentner--Kaminker Definition 2.2: some large-scale Lipschitz map into `E` has
compression exponent strictly above `β₀`.

For `β₀ = 1/2` and `E` a Hilbert space this is the hypothesis of their
Theorem 3.2.  Stating it with a bare exponent rather than with the `liminf` of
Definition 2.2 loses nothing: their proof passes to precisely this form in its
first line. -/
def CompressionExceeds (S : Set G) (β₀ : ℝ) (E : Type v) [NormedAddCommGroup E] :
    Prop :=
  ∃ (f : G → E) (β : ℝ), β₀ < β ∧ IsLargeScaleLipschitz S f ∧
    HasCompressionExponent S f β

/-! ## The Gaussian kernel -/

/-- The Gaussian kernel `u_κ(s,t) = exp(-κ‖f s - f t‖²)` of Guentner--Kaminker
(13).  Their `u_k` is the case `κ = 1/k`. -/
noncomputable def gaussianKernel (f : G → E) (κ : ℝ) (s t : G) : ℝ :=
  Real.exp (-(κ * ‖f s - f t‖ ^ 2))

theorem gaussianKernel_pos (f : G → E) (κ : ℝ) (s t : G) :
    0 < gaussianKernel f κ s t :=
  Real.exp_pos _

theorem gaussianKernel_nonneg (f : G → E) (κ : ℝ) (s t : G) :
    0 ≤ gaussianKernel f κ s t :=
  (gaussianKernel_pos f κ s t).le

theorem gaussianKernel_self (f : G → E) (κ : ℝ) (s : G) :
    gaussianKernel f κ s s = 1 := by
  simp [gaussianKernel]

theorem gaussianKernel_comm (f : G → E) (κ : ℝ) (s t : G) :
    gaussianKernel f κ s t = gaussianKernel f κ t s := by
  rw [gaussianKernel, gaussianKernel, ← norm_neg (f s - f t), neg_sub]

theorem gaussianKernel_le_one {κ : ℝ} (hκ : 0 ≤ κ) (f : G → E) (s t : G) :
    gaussianKernel f κ s t ≤ 1 := by
  rw [gaussianKernel, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (mul_nonneg hκ (sq_nonneg _))

/-- **The convergence condition**, Guentner--Kaminker (8): on a strip
`d(s,t) ≤ R` the kernel is within `κ(CR+D)²` of `1`, so letting `κ → 0` the
kernels tend to `1` uniformly on every strip.  Large-scale Lipschitz is exactly
what makes the bound depend on `R` alone. -/
theorem one_sub_gaussianKernel_le {S : Set G} {f : G → E} {C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ x y : G, ‖f x - f y‖ ≤ C * (WordMetric.wordDist S x y : ℝ) + D)
    {κ : ℝ} (hκ : 0 ≤ κ) (R : ℕ) (s t : G)
    (hst : WordMetric.wordDist S s t ≤ R) :
    1 - gaussianKernel f κ s t ≤ κ * (C * (R : ℝ) + D) ^ 2 := by
  have hdle : (WordMetric.wordDist S s t : ℝ) ≤ (R : ℝ) := by exact_mod_cast hst
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
  have hCD : (0 : ℝ) ≤ C * (R : ℝ) + D := by nlinarith
  have h1 : ‖f s - f t‖ ≤ C * (R : ℝ) + D := by
    refine le_trans (hb s t) ?_
    nlinarith
  have h0 : 0 ≤ ‖f s - f t‖ := norm_nonneg _
  have h2 : ‖f s - f t‖ ^ 2 ≤ (C * (R : ℝ) + D) ^ 2 := by nlinarith [hCD]
  have h3 : (1 : ℝ) - κ * ‖f s - f t‖ ^ 2 ≤ gaussianKernel f κ s t := by
    have hexp := Real.add_one_le_exp (-(κ * ‖f s - f t‖ ^ 2))
    rw [gaussianKernel]
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h2 hκ]

/-! ## Two elementary series bounds -/

private theorem geom_sum_range_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    ∑ i ∈ Finset.range k, q ^ i ≤ (1 - q)⁻¹ := by
  have h1q : 0 < 1 - q := by linarith
  have key : (1 - q) * ∑ i ∈ Finset.range k, q ^ i = 1 - q ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      ring
  have hinv : (1 - q) * (1 - q)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt h1q)
  have h2 : (1 - q) * (∑ i ∈ Finset.range k, q ^ i) ≤ (1 - q) * (1 - q)⁻¹ := by
    rw [hinv, key]
    linarith [pow_nonneg hq0 k]
  exact le_of_mul_le_mul_left h2 h1q

private theorem sum_pow_Ico_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (a b : ℕ) :
    ∑ n ∈ Finset.Ico a b, q ^ n ≤ q ^ a * (1 - q)⁻¹ := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hcongr : ∀ i ∈ Finset.range (b - a), q ^ (a + i) = q ^ a * q ^ i :=
    fun i _ ↦ pow_add q a i
  rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (geom_sum_range_le hq0 hq1 _) (pow_nonneg hq0 a)

private theorem exp_pow_eq (x : ℝ) (n : ℕ) : Real.exp x ^ n = Real.exp (n * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← Real.exp_add]
    congr 1
    push_cast
    ring

/-! ## The estimate (14) -/

/-- **Guentner--Kaminker's estimate (14): the Gaussian rows have uniformly small
tails.**  For every tolerance `δ` there is a radius `N`, depending on nothing
but the data and `δ`, beyond which the kernel mass of every row is at most `δ`.

This is the assertion that lets the truncated kernels `k_n` of their Lemma 3.5
have Schur norm tending to `0`, hence `Op(u_κ)` lie in the uniform Roe algebra.

The proof is theirs.  Exponential growth of the word metric gives `Λⁿ` points
on the sphere of radius `n`; the compression hypothesis gives each of them
weight at most `exp(-κ n^{1+ε})` with `1 + ε = 2β > 1`; and `n^{1+ε} ≥ n · m^ε`
for `n ≥ m` converts the product into the geometric series `(Λ exp(-κ m^ε))ⁿ`,
whose ratio is `< 1` once `m` is large.  Choosing first `m` and then `N`
finishes. -/
theorem exists_tail_bound {T : Finset G}
    (hT : WordMetric.IsSymmetricGeneratingSet (↑T : Set G))
    {f : G → E} {β : ℝ} (hβ : 1 / 2 < β)
    (hcomp : HasCompressionExponent (↑T : Set G) f β)
    {κ : ℝ} (hκ : 0 < κ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ (s : G) (F : Finset G),
      (∀ t ∈ F, N < WordMetric.wordDist (↑T : Set G) s t) →
        ∑ t ∈ F, gaussianKernel f κ s t ≤ δ := by
  classical
  obtain ⟨r₀, hr₀⟩ := hcomp
  set Λ : ℝ := (T.card : ℝ) + 1 with hΛdef
  have hΛ1 : (1 : ℝ) ≤ Λ := WordMetric.one_le_growth T
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ1
  set ε : ℝ := 2 * β - 1 with hεdef
  have hε : 0 < ε := by
    rw [hεdef]; linarith
  -- Step 1: a cut-off radius `m` at which the growth constant is beaten.
  set L : ℝ := max 0 (Real.log (2 * Λ) / κ) with hLdef
  have hL0 : (0 : ℝ) ≤ L := by rw [hLdef]; exact le_max_left _ _
  have hbase : (0 : ℝ) ≤ L + 1 := by linarith
  obtain ⟨m₀, hm₀⟩ := exists_nat_ge ((L + 1) ^ (1 / ε))
  set m : ℕ := max m₀ (max r₀ 1) with hmdef
  have hm1 : 1 ≤ m := by
    rw [hmdef]; exact le_trans (le_max_right r₀ 1) (le_max_right m₀ _)
  have hmr₀ : r₀ ≤ m := by
    rw [hmdef]; exact le_trans (le_max_left r₀ 1) (le_max_right m₀ _)
  have hmm₀ : (m₀ : ℝ) ≤ (m : ℝ) := by
    rw [hmdef]; exact_mod_cast le_max_left m₀ (max r₀ 1)
  have hm0R : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    linarith
  have hxm : ((L + 1) ^ (1 / ε) : ℝ) ≤ (m : ℝ) := le_trans hm₀ hmm₀
  have hmε : L + 1 ≤ (m : ℝ) ^ ε := by
    have h1 : (((L + 1) ^ (1 / ε) : ℝ)) ^ ε = L + 1 := by
      rw [← Real.rpow_mul hbase, one_div, inv_mul_cancel₀ (ne_of_gt hε), Real.rpow_one]
    have h2 : (((L + 1) ^ (1 / ε) : ℝ)) ^ ε ≤ ((m : ℝ)) ^ ε :=
      Real.rpow_le_rpow (Real.rpow_nonneg hbase _) hxm hε.le
    rw [h1] at h2
    exact h2
  -- Step 2: the geometric ratio.
  set q : ℝ := Λ * Real.exp (-(κ * (m : ℝ) ^ ε)) with hqdef
  have hq0 : (0 : ℝ) ≤ q := by
    rw [hqdef]
    exact mul_nonneg hΛ0.le (Real.exp_nonneg _)
  have hκne : κ ≠ 0 := ne_of_gt hκ
  have hΛne : Λ ≠ 0 := ne_of_gt hΛ0
  have hlog : Real.log (2 * Λ) ≤ κ * (m : ℝ) ^ ε := by
    have hle : Real.log (2 * Λ) / κ ≤ L := by rw [hLdef]; exact le_max_right _ _
    have h' : Real.log (2 * Λ) / κ ≤ (m : ℝ) ^ ε := by linarith
    have hrw : Real.log (2 * Λ) = κ * (Real.log (2 * Λ) / κ) := by
      field_simp
    rw [hrw]
    exact mul_le_mul_of_nonneg_left h' hκ.le
  have hqhalf : q ≤ 1 / 2 := by
    have hexp : Real.exp (-(κ * (m : ℝ) ^ ε)) ≤ Real.exp (-(Real.log (2 * Λ))) :=
      Real.exp_le_exp.mpr (by linarith)
    have hval : Real.exp (-(Real.log (2 * Λ))) = (2 * Λ)⁻¹ := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
    rw [hval] at hexp
    have hle : q ≤ Λ * (2 * Λ)⁻¹ := by
      rw [hqdef]
      exact mul_le_mul_of_nonneg_left hexp hΛ0.le
    have hcalc : Λ * (2 * Λ)⁻¹ = 1 / 2 := by
      field_simp
    rw [hcalc] at hle
    exact hle
  have hq1 : q < 1 := by linarith
  have h1q : (0 : ℝ) < 1 - q := by linarith
  -- Step 3: the truncation radius.
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (mul_pos hδ h1q) hq1
  set N : ℕ := max m k with hNdef
  have hNm : m ≤ N := by rw [hNdef]; exact le_max_left _ _
  have hkN : k ≤ N + 1 := by
    rw [hNdef]; exact le_trans (le_max_right m k) (Nat.le_succ _)
  have htailδ : q ^ (N + 1) * (1 - q)⁻¹ ≤ δ := by
    have hmono : q ^ (N + 1) ≤ q ^ k := pow_le_pow_of_le_one hq0 hq1.le hkN
    have hlt : q ^ (N + 1) ≤ δ * (1 - q) := le_of_lt (lt_of_le_of_lt hmono hk)
    have hinv : (0 : ℝ) < (1 - q)⁻¹ := inv_pos.mpr h1q
    have hne : (1 : ℝ) - q ≠ 0 := ne_of_gt h1q
    calc q ^ (N + 1) * (1 - q)⁻¹ ≤ (δ * (1 - q)) * (1 - q)⁻¹ :=
          mul_le_mul_of_nonneg_right hlt hinv.le
      _ = δ := by field_simp
  refine ⟨N, ?_⟩
  intro s F hF
  -- Step 4: slice the row by the sphere the point sits on.
  set M : ℕ := ∑ t ∈ F, WordMetric.wordDist (↑T : Set G) s t
  have hub : ∀ t ∈ F, WordMetric.wordDist (↑T : Set G) s t ≤ M := by
    intro t ht
    exact Finset.single_le_sum (f := fun t ↦ WordMetric.wordDist (↑T : Set G) s t)
      (fun i _ ↦ Nat.zero_le _) ht
  have hmaps : ∀ t ∈ F, WordMetric.wordDist (↑T : Set G) s t ∈ Finset.Ico (N + 1) (M + 1) := by
    intro t ht
    exact Finset.mem_Ico.mpr ⟨hF t ht, Nat.lt_succ_of_le (hub t ht)⟩
  have hslice := Finset.sum_fiberwise_of_maps_to
    (g := fun t ↦ WordMetric.wordDist (↑T : Set G) s t) hmaps (gaussianKernel f κ s)
  -- Step 5: each sphere contributes at most `qⁿ`.
  have hfib : ∀ n ∈ Finset.Ico (N + 1) (M + 1),
      ∑ t ∈ F.filter (fun t ↦ WordMetric.wordDist (↑T : Set G) s t = n),
        gaussianKernel f κ s t ≤ q ^ n := by
    intro n hn
    have hnN : N + 1 ≤ n := (Finset.mem_Ico.mp hn).1
    have hnm : m ≤ n := le_trans hNm (le_trans (Nat.le_succ N) hnN)
    have hn1 : 1 ≤ n := le_trans hm1 hnm
    have hn0R : (0 : ℝ) < (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      linarith
    -- the cardinality of the sphere
    have hcardN : (F.filter (fun t ↦ WordMetric.wordDist (↑T : Set G) s t = n)).card
        ≤ (T.card + 1) ^ n :=
      WordMetric.card_le_pow_of_wordDist_le hT n s _ (by
        intro t ht
        exact le_of_eq (Finset.mem_filter.mp ht).2)
    have hcard : ((F.filter (fun t ↦ WordMetric.wordDist (↑T : Set G) s t = n)).card : ℝ)
        ≤ Λ ^ n := by
      have := (Nat.cast_le (α := ℝ)).mpr hcardN
      rw [hΛdef]
      push_cast at this ⊢
      exact this
    -- the size of each term on that sphere
    have hterm : ∀ t ∈ F.filter (fun t ↦ WordMetric.wordDist (↑T : Set G) s t = n),
        gaussianKernel f κ s t ≤ Real.exp (-(κ * (n : ℝ) ^ (1 + ε))) := by
      intro t ht
      have hd : WordMetric.wordDist (↑T : Set G) s t = n := (Finset.mem_filter.mp ht).2
      have hfar : r₀ ≤ WordMetric.wordDist (↑T : Set G) s t := by
        rw [hd]; exact le_trans hmr₀ hnm
      have hlow : ((n : ℝ)) ^ β ≤ ‖f s - f t‖ := by
        have := hr₀ s t hfar
        rw [hd] at this
        exact this
      have hpos : (0 : ℝ) ≤ ((n : ℝ)) ^ β := Real.rpow_nonneg hn0R.le _
      have hsq : ((n : ℝ)) ^ (1 + ε) ≤ ‖f s - f t‖ ^ 2 := by
        have hmul : (((n : ℝ)) ^ β) * (((n : ℝ)) ^ β) ≤ ‖f s - f t‖ * ‖f s - f t‖ :=
          mul_self_le_mul_self hpos hlow
        have hadd : ((n : ℝ)) ^ (β + β) = (((n : ℝ)) ^ β) * (((n : ℝ)) ^ β) :=
          Real.rpow_add hn0R β β
        have hβε : β + β = 1 + ε := by rw [hεdef]; ring
        rw [pow_two, ← hβε, hadd]
        exact hmul
      rw [gaussianKernel]
      exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hsq hκ.le])
    -- combine
    have hsum : ∑ t ∈ F.filter (fun t ↦ WordMetric.wordDist (↑T : Set G) s t = n),
        gaussianKernel f κ s t
          ≤ ((F.filter (fun t ↦ WordMetric.wordDist (↑T : Set G) s t = n)).card : ℝ)
              * Real.exp (-(κ * (n : ℝ) ^ (1 + ε))) := by
      have := Finset.sum_le_card_nsmul
        (F.filter (fun t ↦ WordMetric.wordDist (↑T : Set G) s t = n))
        (gaussianKernel f κ s) (Real.exp (-(κ * (n : ℝ) ^ (1 + ε)))) hterm
      simpa [nsmul_eq_mul] using this
    have hexpnonneg : (0 : ℝ) ≤ Real.exp (-(κ * (n : ℝ) ^ (1 + ε))) := Real.exp_nonneg _
    have hstep1 : ∑ t ∈ F.filter (fun t ↦ WordMetric.wordDist (↑T : Set G) s t = n),
        gaussianKernel f κ s t ≤ Λ ^ n * Real.exp (-(κ * (n : ℝ) ^ (1 + ε))) :=
      le_trans hsum (mul_le_mul_of_nonneg_right hcard hexpnonneg)
    -- and the geometric comparison
    have hrpow : (n : ℝ) * (m : ℝ) ^ ε ≤ (n : ℝ) ^ (1 + ε) := by
      have hsplit : ((n : ℝ)) ^ (1 + ε) = (n : ℝ) * ((n : ℝ)) ^ ε := by
        rw [Real.rpow_add hn0R, Real.rpow_one]
      have hmn : ((m : ℝ)) ^ ε ≤ ((n : ℝ)) ^ ε := by
        refine Real.rpow_le_rpow hm0R.le ?_ hε.le
        exact_mod_cast hnm
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hmn hn0R.le
    have hexpcmp : Real.exp (-(κ * (n : ℝ) ^ (1 + ε)))
        ≤ Real.exp (-(κ * (m : ℝ) ^ ε)) ^ n := by
      rw [exp_pow_eq]
      exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hrpow hκ.le])
    have hstep2 : Λ ^ n * Real.exp (-(κ * (n : ℝ) ^ (1 + ε))) ≤ q ^ n := by
      rw [hqdef, mul_pow]
      exact mul_le_mul_of_nonneg_left hexpcmp (pow_nonneg hΛ0.le n)
    exact le_trans hstep1 hstep2
  -- Step 6: sum the geometric series.
  calc ∑ t ∈ F, gaussianKernel f κ s t
      = ∑ n ∈ Finset.Ico (N + 1) (M + 1),
          ∑ t ∈ F.filter (fun t ↦ WordMetric.wordDist (↑T : Set G) s t = n),
            gaussianKernel f κ s t := hslice.symm
    _ ≤ ∑ n ∈ Finset.Ico (N + 1) (M + 1), q ^ n := Finset.sum_le_sum hfib
    _ ≤ q ^ (N + 1) * (1 - q)⁻¹ := sum_pow_Ico_le hq0 hq1 _ _
    _ ≤ δ := htailδ

/-- **The Schur test input.**  Every row of the Gaussian kernel has total mass
at most one constant, uniformly in the base point --- Guentner--Kaminker's
"finite and independent of `s ∈ Γ`" after (14).  Together with symmetry of the
kernel this is exactly the hypothesis of their Proposition 3.4 (ii). -/
theorem exists_schur_bound {T : Finset G}
    (hT : WordMetric.IsSymmetricGeneratingSet (↑T : Set G))
    {f : G → E} {β : ℝ} (hβ : 1 / 2 < β)
    (hcomp : HasCompressionExponent (↑T : Set G) f β)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : G) (F : Finset G),
      ∑ t ∈ F, gaussianKernel f κ s t ≤ C := by
  classical
  obtain ⟨N, hN⟩ := exists_tail_bound hT hβ hcomp hκ (δ := 1) one_pos
  refine ⟨((T.card : ℝ) + 1) ^ N + 1, by positivity, ?_⟩
  intro s F
  have hsplit :
      ∑ t ∈ F.filter (fun t ↦ WordMetric.wordDist (↑T : Set G) s t ≤ N),
          gaussianKernel f κ s t
        + ∑ t ∈ F.filter (fun t ↦ ¬ WordMetric.wordDist (↑T : Set G) s t ≤ N),
            gaussianKernel f κ s t
        = ∑ t ∈ F, gaussianKernel f κ s t :=
    Finset.sum_filter_add_sum_filter_not F _ _
  have hnear : ∑ t ∈ F.filter (fun t ↦ WordMetric.wordDist (↑T : Set G) s t ≤ N),
      gaussianKernel f κ s t ≤ ((T.card : ℝ) + 1) ^ N := by
    have hcardN : (F.filter (fun t ↦ WordMetric.wordDist (↑T : Set G) s t ≤ N)).card
        ≤ (T.card + 1) ^ N :=
      WordMetric.card_le_pow_of_wordDist_le hT N s _ (by
        intro t ht
        exact (Finset.mem_filter.mp ht).2)
    have hterm : ∀ t ∈ F.filter (fun t ↦ WordMetric.wordDist (↑T : Set G) s t ≤ N),
        gaussianKernel f κ s t ≤ 1 := fun t _ ↦ gaussianKernel_le_one hκ.le f s t
    have hsum := Finset.sum_le_card_nsmul
      (F.filter (fun t ↦ WordMetric.wordDist (↑T : Set G) s t ≤ N))
      (gaussianKernel f κ s) 1 hterm
    have hcast : ((F.filter (fun t ↦ WordMetric.wordDist (↑T : Set G) s t ≤ N)).card : ℝ)
        ≤ ((T.card : ℝ) + 1) ^ N := by
      have hc := (Nat.cast_le (α := ℝ)).mpr hcardN
      push_cast at hc ⊢
      exact hc
    calc ∑ t ∈ F.filter (fun t ↦ WordMetric.wordDist (↑T : Set G) s t ≤ N),
          gaussianKernel f κ s t
        ≤ ((F.filter (fun t ↦ WordMetric.wordDist (↑T : Set G) s t ≤ N)).card : ℝ) := by
          simpa [nsmul_eq_mul] using hsum
      _ ≤ ((T.card : ℝ) + 1) ^ N := hcast
  have hfar : ∑ t ∈ F.filter (fun t ↦ ¬ WordMetric.wordDist (↑T : Set G) s t ≤ N),
      gaussianKernel f κ s t ≤ 1 := by
    refine hN s _ ?_
    intro t ht
    have := (Finset.mem_filter.mp ht).2
    omega
  linarith [hsplit, hnear, hfar]

end CoarseCompression
end GroupApproximation
