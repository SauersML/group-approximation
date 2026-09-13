import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.Unitary
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Abel

/-!
# Row unitaries of the graph algebras `C*(E(u))`

For a vector `u : Fin n → ℕ`, the graph `E(u)` of the STW Problem L artifact
(`research/artifacts/stw50-six-kirchberg-loops-2026-09-05.md`, §2) has vertices `Fin n`, a loop
`d i` at each vertex, and edges `a i ⟨j, k⟩ : i → j` for `k : Fin (u j)`. This file proves the §2
algebra in an arbitrary star ring carrying a Cuntz–Krieger family of `E(u)`. It does not construct
the universal graph C*-algebra.

* `sum_mul_star_mem_unitary`: rows with `∑ r r* = 1` and the same diagonal `r* r = P` give
  unitaries `∑ r t*`.
* `CuntzKriegerFamily`: the relations `s_a* s_b = δ_ab p_{r(a)}`, `∑_{s(a)=i} s_a s_a* = p_i`,
  `∑ p_i = 1`.
* `CuntzKriegerFamily.p_mul_p`, `star_p`: the vertex elements are orthogonal projections.
* `CuntzKriegerFamily.row`, `sum_row_mul_star_row`, `star_row_mul_row`: Lemma 2.
* `CuntzKriegerFamily.W_mem_unitary`: `W_{i m} = R_i R_m*` is unitary.

Columns of the row `R_i` are `RowIndex u = Fin n ⊕ Σ j, Fin (u j)`: `Sum.inl j` is the printed
column `(j, u_j + 1)` and `Sum.inr ⟨j, k⟩` is `(j, k + 1)`. The products `R_i R_m*` do not depend
on this ordering.
-/

namespace GroupApproximation
namespace KirchbergLoops

open Finset

variable {R : Type*} [Ring R] [StarRing R]

section Rows

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : ι → R}

/-- A row with `∑ r r* = 1` and diagonal `r* r = P` satisfies `r c P c = r c`. -/
theorem mul_rowProj_of_row {r : ι → R} (hr : ∑ c, r c * star (r c) = 1)
    (hrr : ∀ c c', star (r c) * r c' = if c = c' then P c else 0) (c : ι) :
    r c * P c = r c := by
  calc r c * P c = ∑ c', r c' * (star (r c') * r c) := by
        rw [Finset.sum_eq_single c]
        · rw [hrr, if_pos rfl]
        · intro c' _ hc'
          rw [hrr, if_neg hc', mul_zero]
        · intro hc
          exact absurd (Finset.mem_univ c) hc
    _ = r c := by
        simp only [← mul_assoc]
        rw [← Finset.sum_mul, hr, one_mul]

theorem star_mul_sum_of_row {x y : ι → R}
    (hyy : ∀ c c', star (y c) * y c' = if c = c' then P c else 0) (c : ι) :
    star (y c) * ∑ c', y c' * star (x c') = P c * star (x c) := by
  rw [Finset.mul_sum, Finset.sum_eq_single c]
  · rw [← mul_assoc, hyy, if_pos rfl]
  · intro c' _ hc'
    rw [← mul_assoc, hyy, if_neg (Ne.symm hc'), zero_mul]
  · intro hc
    exact absurd (Finset.mem_univ c) hc

theorem sum_mul_star_mul_sum {x x' y : ι → R} (hx' : ∀ c, x' c * P c = x' c)
    (hyy : ∀ c c', star (y c) * y c' = if c = c' then P c else 0) :
    (∑ c, x' c * star (y c)) * ∑ c, y c * star (x c) = ∑ c, x' c * star (x c) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_assoc, star_mul_sum_of_row hyy, ← mul_assoc, hx']

/-- **Row unitaries.** Two rows with `∑ r r* = 1` and the same diagonal `r* r = P` give a
unitary `∑ r t*`. -/
theorem sum_mul_star_mem_unitary {r t : ι → R} (hr : ∑ c, r c * star (r c) = 1)
    (ht : ∑ c, t c * star (t c) = 1)
    (hrr : ∀ c c', star (r c) * r c' = if c = c' then P c else 0)
    (htt : ∀ c c', star (t c) * t c' = if c = c' then P c else 0) :
    ∑ c, r c * star (t c) ∈ unitary R := by
  have hs : star (∑ c, r c * star (t c)) = ∑ c, t c * star (r c) := by
    simp only [star_sum, star_mul, star_star]
  rw [Unitary.mem_iff, hs]
  exact ⟨(sum_mul_star_mul_sum (mul_rowProj_of_row ht htt) hrr).trans ht,
    (sum_mul_star_mul_sum (mul_rowProj_of_row hr hrr) htt).trans hr⟩

end Rows

/-- Edges `a_ij^(k+1)` leaving a fixed vertex `i`, as pairs `⟨j, k⟩` with `k : Fin (u j)`. -/
abbrev ArrowIndex {n : ℕ} (u : Fin n → ℕ) := Σ j : Fin n, Fin (u j)

/-- Columns of a row `R_i`. -/
abbrev RowIndex {n : ℕ} (u : Fin n → ℕ) := Fin n ⊕ ArrowIndex u

/-- **A Cuntz–Krieger family of `E(u)` in a star ring.** -/
structure CuntzKriegerFamily (R : Type*) [Ring R] [StarRing R] (n : ℕ) (u : Fin n → ℕ) where
  /-- Vertex projections. -/
  p : Fin n → R
  /-- The distinguished loops `d_i : i → i`. -/
  d : Fin n → R
  /-- The edges `a_ij^(k+1) : i → j`, indexed by `⟨j, k⟩`. -/
  a : Fin n → ArrowIndex u → R
  star_d_mul_d : ∀ i i', star (d i) * d i' = if i = i' then p i else 0
  star_d_mul_a : ∀ i i' e, star (d i) * a i' e = 0
  star_a_mul_a : ∀ i e i' e', star (a i e) * a i' e' = if i = i' ∧ e = e' then p e.1 else 0
  sum_source : ∀ i, d i * star (d i) + ∑ e, a i e * star (a i e) = p i
  sum_p : ∑ i, p i = 1

namespace CuntzKriegerFamily

variable {n : ℕ} {u : Fin n → ℕ} (F : CuntzKriegerFamily R n u)

theorem star_a_mul_d (i : Fin n) (e : ArrowIndex u) (i' : Fin n) :
    star (F.a i e) * F.d i' = 0 := by
  have h := congrArg star (F.star_d_mul_a i' i e)
  simpa only [star_mul, star_star, star_zero] using h

theorem p_mul_d_of_ne {j i : Fin n} (h : j ≠ i) : F.p j * F.d i = 0 := by
  rw [← F.sum_source j, add_mul, Finset.sum_mul, mul_assoc, F.star_d_mul_d, if_neg h, mul_zero,
    zero_add]
  exact Finset.sum_eq_zero fun e _ => by rw [mul_assoc, F.star_a_mul_d, mul_zero]

theorem p_mul_a_of_ne {j i : Fin n} (h : j ≠ i) (e : ArrowIndex u) : F.p j * F.a i e = 0 := by
  rw [← F.sum_source j, add_mul, Finset.sum_mul, mul_assoc, F.star_d_mul_a, mul_zero, zero_add]
  refine Finset.sum_eq_zero fun e' _ => ?_
  have hne : ¬(j = i ∧ e' = e) := fun h' => h h'.1
  rw [mul_assoc, F.star_a_mul_a, if_neg hne, mul_zero]

theorem p_mul_d_self (i : Fin n) : F.p i * F.d i = F.d i := by
  have h : ∑ j, F.p j * F.d i = F.p i * F.d i :=
    Finset.sum_eq_single i (fun j _ hj => F.p_mul_d_of_ne hj) fun hi =>
      absurd (Finset.mem_univ i) hi
  rw [← h, ← Finset.sum_mul, F.sum_p, one_mul]

theorem p_mul_a_self (i : Fin n) (e : ArrowIndex u) : F.p i * F.a i e = F.a i e := by
  have h : ∑ j, F.p j * F.a i e = F.p i * F.a i e :=
    Finset.sum_eq_single i (fun j _ hj => F.p_mul_a_of_ne hj e) fun hi =>
      absurd (Finset.mem_univ i) hi
  rw [← h, ← Finset.sum_mul, F.sum_p, one_mul]

theorem star_p (i : Fin n) : star (F.p i) = F.p i := by
  have h := F.star_d_mul_d i i
  rw [if_pos rfl] at h
  rw [← h, star_mul, star_star]

theorem p_mul_p (i j : Fin n) : F.p i * F.p j = if i = j then F.p i else 0 := by
  conv_lhs => rw [← F.sum_source j]
  rw [mul_add, Finset.mul_sum, ← mul_assoc]
  by_cases h : i = j
  · rw [← h, if_pos rfl, F.p_mul_d_self]
    conv_rhs => rw [← F.sum_source i]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← mul_assoc, F.p_mul_a_self]
  · rw [if_neg h, F.p_mul_d_of_ne h, zero_mul, zero_add]
    exact Finset.sum_eq_zero fun e _ => by rw [← mul_assoc, F.p_mul_a_of_ne h, zero_mul]

/-- The row `R_i` of (3). -/
def row (i : Fin n) : RowIndex u → R :=
  Sum.elim (fun j => if j = i then F.d i else F.p j) (F.a i)

/-- The range projection `R_i* R_i`, the same for every `i`. -/
def rowProj : RowIndex u → R :=
  Sum.elim F.p fun e => F.p e.1

theorem row_inl (i j : Fin n) : F.row i (.inl j) = if j = i then F.d i else F.p j := rfl

theorem row_inr (i : Fin n) (e : ArrowIndex u) : F.row i (.inr e) = F.a i e := rfl

theorem rowProj_inl (j : Fin n) : F.rowProj (.inl j) = F.p j := rfl

theorem rowProj_inr (e : ArrowIndex u) : F.rowProj (.inr e) = F.p e.1 := rfl

/-- **Lemma 2, first half: `R_i R_i* = 1`.** -/
theorem sum_row_mul_star_row (i : Fin n) : ∑ c, F.row i c * star (F.row i c) = 1 := by
  have h : ∀ j, F.row i (.inl j) * star (F.row i (.inl j)) =
      F.p j - if j = i then ∑ e, F.a i e * star (F.a i e) else 0 := by
    intro j
    by_cases hj : j = i
    · rw [hj, row_inl, if_pos rfl, if_pos rfl, ← F.sum_source i]
      abel
    · rw [row_inl, if_neg hj, if_neg hj, sub_zero, F.star_p, F.p_mul_p, if_pos rfl]
  rw [Fintype.sum_sum_type]
  simp only [h, row_inr]
  rw [Finset.sum_sub_distrib, F.sum_p, Finset.sum_ite_eq', if_pos (Finset.mem_univ i),
    sub_add_cancel]

/-- **Lemma 2, second half: `R_i* R_i = P`.** -/
theorem star_row_mul_row (i : Fin n) (c c' : RowIndex u) :
    star (F.row i c) * F.row i c' = if c = c' then F.rowProj c else 0 := by
  rcases c with j | e <;> rcases c' with j' | e'
  · rw [row_inl, row_inl, rowProj_inl]
    by_cases hj : j = i <;> by_cases hj' : j' = i
    · have hc : (Sum.inl j : RowIndex u) = Sum.inl j' := congrArg Sum.inl (hj.trans hj'.symm)
      rw [if_pos hj, if_pos hj', F.star_d_mul_d, if_pos rfl, if_pos hc, hj]
    · have hc : (Sum.inl j : RowIndex u) ≠ Sum.inl j' := fun h =>
        hj' ((Sum.inl_injective h).symm.trans hj)
      rw [if_pos hj, if_neg hj', ← F.star_p j', ← star_mul, F.p_mul_d_of_ne hj', star_zero,
        if_neg hc]
    · have hc : (Sum.inl j : RowIndex u) ≠ Sum.inl j' := fun h =>
        hj ((Sum.inl_injective h).trans hj')
      rw [if_neg hj, if_pos hj', F.star_p, F.p_mul_d_of_ne hj, if_neg hc]
    · rw [if_neg hj, if_neg hj', F.star_p, F.p_mul_p]
      by_cases hjj : j = j'
      · have hc : (Sum.inl j : RowIndex u) = Sum.inl j' := congrArg Sum.inl hjj
        rw [if_pos hjj, if_pos hc]
      · have hc : (Sum.inl j : RowIndex u) ≠ Sum.inl j' := fun h => hjj (Sum.inl_injective h)
        rw [if_neg hjj, if_neg hc]
  · have hc : (Sum.inl j : RowIndex u) ≠ Sum.inr e' := Sum.inl_ne_inr
    rw [row_inl, row_inr, if_neg hc]
    by_cases hj : j = i
    · rw [if_pos hj, F.star_d_mul_a]
    · rw [if_neg hj, F.star_p, F.p_mul_a_of_ne hj]
  · have hc : (Sum.inr e : RowIndex u) ≠ Sum.inl j' := Sum.inr_ne_inl
    rw [row_inr, row_inl, if_neg hc]
    by_cases hj' : j' = i
    · rw [if_pos hj', F.star_a_mul_d]
    · rw [if_neg hj', ← F.star_p j', ← star_mul, F.p_mul_a_of_ne hj', star_zero]
  · rw [row_inr, row_inr, rowProj_inr, F.star_a_mul_a]
    by_cases he : e = e'
    · have hc : (Sum.inr e : RowIndex u) = Sum.inr e' := congrArg Sum.inr he
      rw [if_pos (And.intro rfl he), if_pos hc]
    · have h₁ : ¬(i = i ∧ e = e') := fun h => he h.2
      have h₂ : (Sum.inr e : RowIndex u) ≠ Sum.inr e' := fun h => he (Sum.inr_injective h)
      rw [if_neg h₁, if_neg h₂]

/-- The unitary `W_{i m} = R_i R_m*`. The artifact's `W_i` is `W_{i n}`. -/
def W (i m : Fin n) : R := ∑ c, F.row i c * star (F.row m c)

/-- **`W_{i m} = R_i R_m*` is unitary.** -/
theorem W_mem_unitary (i m : Fin n) : F.W i m ∈ unitary R :=
  sum_mul_star_mem_unitary (F.sum_row_mul_star_row i) (F.sum_row_mul_star_row m)
    (F.star_row_mul_row i) (F.star_row_mul_row m)

end CuntzKriegerFamily

end KirchbergLoops
end GroupApproximation
