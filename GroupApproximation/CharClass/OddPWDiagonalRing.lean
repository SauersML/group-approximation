import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# The coefficients of the resolution coproduct `ψ_W`, as ring identities

`notes/lix-stronger-lane-reports/sp-steenrod.md` §6.2: the Cartan formula at an odd prime needs a
`Λ`-linear, counital chain map `ψ : W → W ⊗_{F_p} W`, `Λ = F_p[ℤ/p]` acting diagonally, where `W`
is the periodic resolution (`Wodd`, differentials `T − 1` into even degrees and `N` into odd ones).
`sp-design` solved the recursion; the closed form is

```text
ψ(e_n) = Σ_{a+b=n}   e_a ⊗ e_b                              a even
                     e_a ⊗ T e_b                            a odd, b even
                     Σ_{0 ≤ u < v < p} T^u e_a ⊗ T^v e_b       a, b both odd
```

In bidegree `(a, b)` the tensor square `W_a ⊗ W_b` is the group ring of `ℤ/p × ℤ/p`, with `T₁`
acting on the left factor and `T₂` on the right, so the coefficient of `ψ(e_n)` there is an element
`φ(a, b)` of a commutative ring: `1`, `T₂`, or `Q = Σ_{u<v} T₁^u T₂^v`.  The chain-map condition
read in bidegree `(a, b)` is

```text
c_a(T₁) φ(a+1, b) + (−1)^a c_b(T₂) φ(a, b+1) = c_{a+b}(T₁T₂) φ(a, b),
c_k(t) = t − 1 (k even),  N(t) = 1 + t + ⋯ + t^{p−1} (k odd),
```

and this file proves it in **any** commutative ring, for any two elements with `T₂^m = 1`
(`wdChain_identity`).  Nothing about `ZMod p`, and `T₁^m = 1` is never used.  The four parity cases
reduce to three identities about `Q`, each proved by induction on `m` with no reindexing of sums:

* `wdQSum_mul_left`  : `(T₁ − 1) Q = N(T₁T₂) − N(T₂)`, with no relation at all;
* `wdQSum_mul_right` : `(T₂ − 1) Q = T₂^m N(T₁) − T₂ N(T₁T₂)`, with no relation at all;
* `wdQSum_mul_diag`  : `(T₁T₂ − 1) Q = N(T₁) − N(T₂)`, using `T₂^m = 1`.

The **reduced coefficients** `c̄(a, b)`, the images under the augmentation `T₁, T₂ ↦ 1`, are `1`,
`1` and `Σ_{v<p} v = p(p−1)/2`; the last is `0` in `F_p` for `p` odd (`wdQSum_one_one_zmod`).

The model test (`notes/lix-stronger-lane-reports/tools/psiw_test.py`, run on acn112) checked the bidegree identity, the counits and the reduced coefficients at `p = 3, 5, 7` for
every `n ≤ 2(p−1) + 3`.
-/

namespace GroupApproximation.CharClass

open Finset

section Ring

variable {S : Type*} [CommRing S]

/-- `N_m(t) = 1 + t + ⋯ + t^{m-1}`. -/
def wdNormSum (m : ℕ) (t : S) : S := ∑ j ∈ range m, t ^ j

/-- The differential coefficient of the periodic resolution out of degree `k + 1`: `t − 1` into an
even degree, the norm `N_m(t)` into an odd one.  At `t = T` this is `altCoeff (grS p) (grNorm p) k`. -/
def wdCAlt (m k : ℕ) (t : S) : S := if Even k then t - 1 else wdNormSum m t

/-- `Q_m = Σ_{0 ≤ u < v < m} T₁^u T₂^v`. -/
def wdQSum (m : ℕ) (T₁ T₂ : S) : S := ∑ v ∈ range m, ∑ u ∈ range v, T₁ ^ u * T₂ ^ v

/-- **The coefficient of `ψ(e_n)` in bidegree `(a, b)`**: `1` for `a` even, `T₂` for `a` odd and
`b` even, `Q` for both odd. -/
def wdPhi (m a b : ℕ) (T₁ T₂ : S) : S :=
  if Even a then 1 else if Even b then T₂ else wdQSum m T₁ T₂

theorem wdNormSum_zero (t : S) : wdNormSum 0 t = 0 := by simp [wdNormSum]

theorem wdNormSum_succ (m : ℕ) (t : S) : wdNormSum (m + 1) t = wdNormSum m t + t ^ m :=
  sum_range_succ _ _

theorem wdQSum_zero (T₁ T₂ : S) : wdQSum 0 T₁ T₂ = 0 := by simp [wdQSum]

theorem wdQSum_succ (m : ℕ) (T₁ T₂ : S) :
    wdQSum (m + 1) T₁ T₂ = wdQSum m T₁ T₂ + wdNormSum m T₁ * T₂ ^ m := by
  simp only [wdQSum, wdNormSum, sum_range_succ, sum_mul]

/-- `t · N_m(t) = N_m(t) − 1 + t^m`. -/
theorem wdMul_normSum (m : ℕ) (t : S) : t * wdNormSum m t = wdNormSum m t - 1 + t ^ m := by
  induction m with
  | zero => simp [wdNormSum]
  | succ m ih =>
      rw [wdNormSum_succ, mul_add, ih]
      ring

/-- `(T₁ − 1) Q = N(T₁T₂) − N(T₂)`, with no relation. -/
theorem wdQSum_mul_left (m : ℕ) (T₁ T₂ : S) :
    (T₁ - 1) * wdQSum m T₁ T₂ = wdNormSum m (T₁ * T₂) - wdNormSum m T₂ := by
  induction m with
  | zero => simp [wdQSum, wdNormSum]
  | succ m ih =>
      rw [wdQSum_succ, wdNormSum_succ, wdNormSum_succ]
      linear_combination ih + T₂ ^ m * wdMul_normSum m T₁

/-- `(T₂ − 1) Q = T₂^m N(T₁) − T₂ N(T₁T₂)`, with no relation. -/
theorem wdQSum_mul_right_raw (m : ℕ) (T₁ T₂ : S) :
    (T₂ - 1) * wdQSum m T₁ T₂ = T₂ ^ m * wdNormSum m T₁ - T₂ * wdNormSum m (T₁ * T₂) := by
  induction m with
  | zero => simp [wdQSum, wdNormSum]
  | succ m ih =>
      rw [wdQSum_succ, wdNormSum_succ, wdNormSum_succ]
      linear_combination ih

/-- `(T₂ − 1) Q = N(T₁) − T₂ N(T₁T₂)`, when `T₂^m = 1`. -/
theorem wdQSum_mul_right (m : ℕ) {T₁ T₂ : S} (h₂ : T₂ ^ m = 1) :
    (T₂ - 1) * wdQSum m T₁ T₂ = wdNormSum m T₁ - T₂ * wdNormSum m (T₁ * T₂) := by
  linear_combination wdQSum_mul_right_raw m T₁ T₂ + wdNormSum m T₁ * h₂

/-- `(T₁T₂ − 1) Q = N(T₁) − N(T₂)`, when `T₂^m = 1`. -/
theorem wdQSum_mul_diag (m : ℕ) {T₁ T₂ : S} (h₂ : T₂ ^ m = 1) :
    (T₁ * T₂ - 1) * wdQSum m T₁ T₂ = wdNormSum m T₁ - wdNormSum m T₂ := by
  linear_combination T₁ * wdQSum_mul_right_raw m T₁ T₂ + wdQSum_mul_left m T₁ T₂
    + T₂ ^ m * wdMul_normSum m T₁ - wdMul_normSum m (T₁ * T₂) + (wdNormSum m T₁ - 1) * h₂

/-- **The chain-map condition of `ψ_W` in bidegree `(a, b)`.** -/
theorem wdChain_identity (m : ℕ) {T₁ T₂ : S} (h₂ : T₂ ^ m = 1) (a b : ℕ) :
    wdCAlt m a T₁ * wdPhi m (a + 1) b T₁ T₂
        + (-1 : S) ^ a * (wdCAlt m b T₂ * wdPhi m a (b + 1) T₁ T₂)
      = wdCAlt m (a + b) (T₁ * T₂) * wdPhi m a b T₁ T₂ := by
  have hA1 : Even (a + 1) ↔ ¬ Even a := Nat.even_add_one
  have hB1 : Even (b + 1) ↔ ¬ Even b := Nat.even_add_one
  have hAB : Even (a + b) ↔ (Even a ↔ Even b) := Nat.even_add
  by_cases ha : Even a <;> by_cases hb : Even b
  · have e1 : ¬ Even (a + 1) := fun h => (hA1.mp h) ha
    have e2 : ¬ Even (b + 1) := fun h => (hB1.mp h) hb
    have e3 : Even (a + b) := hAB.mpr (iff_of_true ha hb)
    simp only [wdCAlt, wdPhi, if_pos ha, if_pos hb, if_neg e1, if_neg e2, if_pos e3,
      ha.neg_one_pow]
    ring
  · have e1 : ¬ Even (a + 1) := fun h => (hA1.mp h) ha
    have e2 : Even (b + 1) := hB1.mpr hb
    have e3 : ¬ Even (a + b) := fun h => hb ((hAB.mp h).mp ha)
    simp only [wdCAlt, wdPhi, if_pos ha, if_neg hb, if_neg e1, if_pos e2, if_neg e3,
      ha.neg_one_pow]
    linear_combination wdQSum_mul_left m T₁ T₂
  · have e1 : Even (a + 1) := hA1.mpr ha
    have e2 : ¬ Even (b + 1) := fun h => (hB1.mp h) hb
    have e3 : ¬ Even (a + b) := fun h => ha ((hAB.mp h).mpr hb)
    simp only [wdCAlt, wdPhi, if_neg ha, if_pos hb, if_pos e1, if_neg e2, if_neg e3,
      (Nat.not_even_iff_odd.mp ha).neg_one_pow]
    linear_combination (-1 : S) * wdQSum_mul_right m h₂
  · have e1 : Even (a + 1) := hA1.mpr ha
    have e2 : Even (b + 1) := hB1.mpr hb
    have e3 : Even (a + b) := hAB.mpr (iff_of_false ha hb)
    simp only [wdCAlt, wdPhi, if_neg ha, if_neg hb, if_pos e1, if_pos e2, if_pos e3,
      (Nat.not_even_iff_odd.mp ha).neg_one_pow]
    linear_combination (-1 : S) * wdQSum_mul_diag m h₂ - wdMul_normSum m T₂ - h₂

/-- The augmentation of `Q_m` is `Σ_{v<m} v`. -/
theorem wdQSum_one_one (m : ℕ) : wdQSum m (1 : S) 1 = ((∑ v ∈ range m, v : ℕ) : S) := by
  simp [wdQSum, Nat.cast_sum]

end Ring

/-- **The odd×odd reduced coefficient vanishes**: `Σ_{v<p} v = p · (p−1)/2 ≡ 0 (mod p)` for `p`
odd.  At `p = 2` it is `1`, which is why the mod-2 coproduct has no such term to kill. -/
theorem wdQSum_one_one_zmod {p : ℕ} (hp : Odd p) : wdQSum p (1 : ZMod p) 1 = 0 := by
  rw [wdQSum_one_one]
  obtain ⟨k, rfl⟩ := hp
  have h2 := sum_range_id_mul_two (2 * k + 1)
  have hs : (∑ i ∈ range (2 * k + 1), i) = (2 * k + 1) * k := by
    refine Nat.eq_of_mul_eq_mul_right two_pos ?_
    rw [h2, Nat.add_sub_cancel]
    ring
  rw [hs, Nat.cast_mul, ZMod.natCast_self, zero_mul]

/-- The reduced coefficients: `1` when `a` is even. -/
theorem wdPhi_one_one_even {S : Type*} [CommRing S] (m : ℕ) {a b : ℕ} (ha : Even a) :
    wdPhi m a b (1 : S) 1 = 1 := by
  simp [wdPhi, ha]

/-- The reduced coefficients: `1` when `a` is odd and `b` even. -/
theorem wdPhi_one_one_odd_even {S : Type*} [CommRing S] (m : ℕ) {a b : ℕ} (ha : ¬ Even a)
    (hb : Even b) : wdPhi m a b (1 : S) 1 = 1 := by
  simp [wdPhi, ha, hb]

/-- **The reduced coefficients: `0` when `a` and `b` are both odd**, at an odd prime. -/
theorem wdPhi_one_one_odd_odd {p : ℕ} (hp : Odd p) {a b : ℕ} (ha : ¬ Even a) (hb : ¬ Even b) :
    wdPhi p a b (1 : ZMod p) 1 = 0 := by
  simp only [wdPhi, if_neg ha, if_neg hb]
  exact wdQSum_one_one_zmod hp

end GroupApproximation.CharClass

open GroupApproximation.CharClass

#audit_axioms wdQSum_mul_left
#audit_axioms wdQSum_mul_diag
#audit_axioms wdChain_identity
#audit_axioms wdQSum_one_one_zmod
#audit_axioms wdPhi_one_one_odd_odd
