import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Analysis.SpecificLimits.Basic
import GroupApproximation.Manuscript.SimpleKazhdanSofic.WordProblemDegreeStatements
import GroupApproximation.Meta.AxiomGuard

/-!
# The irrational number `[0; a_0, a_1, …]` for digits in `{1, 2}`

`simple_kazhdan_sofic_group.tex` (origin tip 696c4b602), proof of `cor:wp`, second paragraph:

> Every `S ⊆ ℕ` has the degree of `[0; 1 + χ_S(0), 1 + χ_S(1), …]`, since each digit is decided by
> one strict comparison with a rational computed from earlier digits.

This module constructs the number and its continued fraction expansion. For digits `a_k ∈ {1, 2}`,
the tails `y_k = [0; a_k, a_{k+1}, …]` are limits of the approximations
`approx (n + 1) k = (a_k + approx n (k + 1))⁻¹`, which stay in `[1/3, 3/4]` and contract by `9/16`.
The limits satisfy `y_k = (a_k + y_{k+1})⁻¹`, so the continued fraction algorithm reads off
`⌊y_k⁻¹⌋ = a_k` and passes to `y_{k+1}`:
* `isContinuedFractionOf_tail`: `GenContFract.of y_0` has integer part `0` and partial
  denominators `a`;
* `irrational_tail`: `y_0` is irrational, since its expansion does not terminate.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace ContinuedFractionExpansion

open Filter Topology

variable (a : ℕ → ℕ)

/-- `approx n k`: the tail `[0; a_k, a_{k+1}, …]` truncated after `n` digits, started at `1/2`. -/
noncomputable def approx : ℕ → ℕ → ℝ
  | 0 => fun _ => 1 / 2
  | n + 1 => fun k => ((a k : ℝ) + approx n (k + 1))⁻¹

theorem digit_bounds {a : ℕ → ℕ} (ha : ∀ k, a k = 1 ∨ a k = 2) (k : ℕ) :
    (1 : ℝ) ≤ a k ∧ (a k : ℝ) ≤ 2 := by
  rcases ha k with h | h <;> rw [h] <;> norm_num

theorem approx_mem (ha : ∀ k, a k = 1 ∨ a k = 2) :
    ∀ n k, approx a n k ∈ Set.Icc (1 / 3 : ℝ) (3 / 4) := by
  intro n
  induction n with
  | zero => intro k; exact ⟨by norm_num [approx], by norm_num [approx]⟩
  | succ n ih =>
    intro k
    obtain ⟨h1, h2⟩ := ih (k + 1)
    obtain ⟨hk1, hk2⟩ := digit_bounds ha k
    have hpos : (0 : ℝ) < a k + approx a n (k + 1) := by linarith
    show 1 / 3 ≤ ((a k : ℝ) + approx a n (k + 1))⁻¹ ∧ ((a k : ℝ) + approx a n (k + 1))⁻¹ ≤ 3 / 4
    rw [← one_div]
    constructor
    · rw [le_div_iff₀ hpos]; linarith
    · rw [div_le_iff₀ hpos]; linarith

theorem approx_dist (ha : ∀ k, a k = 1 ∨ a k = 2) :
    ∀ n k, |approx a n k - approx a (n + 1) k| ≤ (9 / 16 : ℝ) ^ n := by
  intro n
  induction n with
  | zero =>
    intro k
    obtain ⟨h1, h2⟩ := approx_mem a ha 1 k
    have h0 : approx a 0 k = 1 / 2 := rfl
    rw [pow_zero, h0, abs_sub_le_iff]
    constructor <;> linarith
  | succ n ih =>
    intro k
    obtain ⟨x1, -⟩ := approx_mem a ha n (k + 1)
    obtain ⟨y1, -⟩ := approx_mem a ha (n + 1) (k + 1)
    obtain ⟨hk1, -⟩ := digit_bounds ha k
    have hA : (4 / 3 : ℝ) ≤ a k + approx a n (k + 1) := by linarith
    have hB : (4 / 3 : ℝ) ≤ a k + approx a (n + 1) (k + 1) := by linarith
    have hA0 : (0 : ℝ) < a k + approx a n (k + 1) := by linarith
    have hB0 : (0 : ℝ) < a k + approx a (n + 1) (k + 1) := by linarith
    have e : approx a (n + 1) k - approx a (n + 1 + 1) k =
        (approx a (n + 1) (k + 1) - approx a n (k + 1)) /
          (((a k : ℝ) + approx a n (k + 1)) * ((a k : ℝ) + approx a (n + 1) (k + 1))) := by
      show ((a k : ℝ) + approx a n (k + 1))⁻¹ - ((a k : ℝ) + approx a (n + 1) (k + 1))⁻¹ = _
      rw [inv_sub_inv hA0.ne' hB0.ne']
      ring
    have hP : (16 / 9 : ℝ) ≤ ((a k : ℝ) + approx a n (k + 1)) *
        ((a k : ℝ) + approx a (n + 1) (k + 1)) := by nlinarith
    rw [e, abs_div, abs_of_pos (mul_pos hA0 hB0), div_le_iff₀ (mul_pos hA0 hB0)]
    calc |approx a (n + 1) (k + 1) - approx a n (k + 1)|
        = |approx a n (k + 1) - approx a (n + 1) (k + 1)| := abs_sub_comm _ _
      _ ≤ (9 / 16) ^ n := ih (k + 1)
      _ = (9 / 16) ^ (n + 1) * (16 / 9) := by ring
      _ ≤ (9 / 16) ^ (n + 1) * (((a k : ℝ) + approx a n (k + 1)) *
          ((a k : ℝ) + approx a (n + 1) (k + 1))) := by gcongr

theorem exists_tendsto_approx (ha : ∀ k, a k = 1 ∨ a k = 2) (k : ℕ) :
    ∃ y, Tendsto (fun n => approx a n k) atTop (𝓝 y) :=
  cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric (r := (9 / 16 : ℝ)) (C := 1)
    (by norm_num) fun n => by
      rw [Real.dist_eq, one_mul]
      exact approx_dist a ha n k)

/-- The tail `y_k = [0; a_k, a_{k+1}, …]`. -/
noncomputable def tail (ha : ∀ k, a k = 1 ∨ a k = 2) (k : ℕ) : ℝ :=
  (exists_tendsto_approx a ha k).choose

variable {a}

theorem tendsto_tail (ha : ∀ k, a k = 1 ∨ a k = 2) (k : ℕ) :
    Tendsto (fun n => approx a n k) atTop (𝓝 (tail a ha k)) :=
  (exists_tendsto_approx a ha k).choose_spec

theorem tail_mem (ha : ∀ k, a k = 1 ∨ a k = 2) (k : ℕ) : tail a ha k ∈ Set.Icc (1 / 3 : ℝ) (3 / 4) :=
  isClosed_Icc.mem_of_tendsto (tendsto_tail ha k)
    (Eventually.of_forall fun n => approx_mem a ha n k)

/-- `y_k = (a_k + y_{k+1})⁻¹`. -/
theorem tail_eq (ha : ∀ k, a k = 1 ∨ a k = 2) (k : ℕ) :
    tail a ha k = ((a k : ℝ) + tail a ha (k + 1))⁻¹ := by
  have h1 : Tendsto (fun n => approx a (n + 1) k) atTop (𝓝 (tail a ha k)) :=
    (tendsto_add_atTop_iff_nat 1).2 (tendsto_tail ha k)
  have hne : (a k : ℝ) + tail a ha (k + 1) ≠ 0 := by
    have h := (tail_mem ha (k + 1)).1
    have h0 : (0 : ℝ) ≤ a k := Nat.cast_nonneg _
    exact (by linarith : (0 : ℝ) < a k + tail a ha (k + 1)).ne'
  have h2 : Tendsto (fun n => approx a (n + 1) k) atTop
      (𝓝 (((a k : ℝ) + tail a ha (k + 1))⁻¹)) :=
    ((tendsto_tail ha (k + 1)).const_add (a k : ℝ)).inv₀ hne
  exact tendsto_nhds_unique h1 h2

theorem fract_tail (ha : ∀ k, a k = 1 ∨ a k = 2) (k : ℕ) : Int.fract (tail a ha k) = tail a ha k :=
  Int.fract_eq_self.2 ⟨by linarith [(tail_mem ha k).1], by linarith [(tail_mem ha k).2]⟩

theorem fract_tail_ne_zero (ha : ∀ k, a k = 1 ∨ a k = 2) (k : ℕ) : Int.fract (tail a ha k) ≠ 0 := by
  rw [fract_tail ha k]
  exact (by linarith [(tail_mem ha k).1] : (0 : ℝ) < tail a ha k).ne'

/-- Adding a natural number does not change the coefficient sequence. -/
theorem of_s_get?_natCast_add (m : ℕ) {y : ℝ} (hy : Int.fract y ≠ 0) (j : ℕ) :
    (GenContFract.of ((m : ℝ) + y)).s.get? j = (GenContFract.of y).s.get? j := by
  have hf : Int.fract ((m : ℝ) + y) = Int.fract y := Int.fract_natCast_add m y
  cases j with
  | zero =>
    change (GenContFract.of ((m : ℝ) + y)).s.head = (GenContFract.of y).s.head
    rw [GenContFract.of_s_head (by rw [hf]; exact hy), GenContFract.of_s_head hy, hf]
  | succ j => rw [GenContFract.of_s_succ, GenContFract.of_s_succ, hf]

theorem floor_digit_add_tail (ha : ∀ k, a k = 1 ∨ a k = 2) (k : ℕ) :
    ⌊(a k : ℝ) + tail a ha (k + 1)⌋ = (a k : ℤ) := by
  rw [Int.floor_natCast_add, Int.floor_eq_zero_iff.2
    ⟨by linarith [(tail_mem ha (k + 1)).1], by linarith [(tail_mem ha (k + 1)).2]⟩, add_zero]

/-- The coefficients of `GenContFract.of y_k` are `⟨1, a_{k+j}⟩`. -/
theorem of_tail_s_get? (ha : ∀ k, a k = 1 ∨ a k = 2) :
    ∀ j k, (GenContFract.of (tail a ha k)).s.get? j = some ⟨1, (a (k + j) : ℝ)⟩ := by
  intro j
  induction j with
  | zero =>
    intro k
    change (GenContFract.of (tail a ha k)).s.head = _
    rw [GenContFract.of_s_head (fract_tail_ne_zero ha k), fract_tail ha k, tail_eq ha k, inv_inv,
      floor_digit_add_tail ha k, Int.cast_natCast, add_zero]
  | succ j ih =>
    intro k
    rw [GenContFract.of_s_succ, fract_tail ha k, tail_eq ha k, inv_inv,
      of_s_get?_natCast_add (a k) (fract_tail_ne_zero ha (k + 1)) j, ih (k + 1),
      show k + 1 + j = k + (j + 1) by omega]

/-- `GenContFract.of y_0` has integer part `0` and partial denominators `a`. -/
theorem isContinuedFractionOf_tail (ha : ∀ k, a k = 1 ∨ a k = 2) :
    IsContinuedFractionOf (tail a ha 0) a := by
  refine ⟨?_, fun k => ?_⟩
  · rw [GenContFract.of_h_eq_floor, Int.floor_eq_zero_iff.2
      ⟨by linarith [(tail_mem ha 0).1], by linarith [(tail_mem ha 0).2]⟩, Int.cast_zero]
  · rw [GenContFract.partDens, Stream'.Seq.map_get?, of_tail_s_get? ha k 0, zero_add]
    rfl

/-- `y_k` is irrational: its continued fraction expansion does not terminate. -/
theorem irrational_tail (ha : ∀ k, a k = 1 ∨ a k = 2) (k : ℕ) : Irrational (tail a ha k) := by
  rintro ⟨q, hq⟩
  obtain ⟨n, hn⟩ := (GenContFract.terminates_iff_rat (tail a ha k)).2 ⟨q, hq.symm⟩
  have hn' : (GenContFract.of (tail a ha k)).s.get? n = none := hn
  rw [of_tail_s_get? ha n k] at hn'
  exact Option.some_ne_none _ hn'

open Classical in
theorem printedDigits_one_or_two (B : Set ℕ) :
    ∀ k, (fun k => 1 + if k ∈ B then 1 else 0) k = 1 ∨ (fun k => 1 + if k ∈ B then 1 else 0) k = 2 := by
  intro k
  by_cases h : k ∈ B <;> simp [h]

#audit_axioms isContinuedFractionOf_tail
#audit_axioms irrational_tail
#audit_axioms tail_eq

end ContinuedFractionExpansion
end SimpleKazhdanSofic
end GroupApproximation
