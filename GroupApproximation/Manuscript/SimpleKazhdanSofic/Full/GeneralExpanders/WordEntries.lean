import GroupApproximation.Leavitt.ElementaryGroup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Entrywise approximation of words by asymptotically multiplicative maps

`simple_kazhdan_sofic_group.tex`, `thm:general` (b), tex l.178–189, and the proof in the
section "Finite simple models", tex l.317–342.

The printed hypotheses on the maps `φ_k : R → M_{N_k}(𝔽₂)` say that for all `r, r'` and all
large `k`, `φ_k(r + r') = φ_k(r) + φ_k(r')` and `φ_k(r r') = φ_k(r) φ_k(r')`, and that
`φ_k(1) = I`. The first step of the printed proof is:

> a word in the generators that is trivial in `G` is trivial in the finite models for large `k`,
> because only finitely many entries and ring operations are involved.

This file proves exactly that step, over an arbitrary index type of rows and arbitrary target
rings `M k`. A matrix over `R` is *entrywise approximated* by a sequence of matrices over the
`M k` if, for large `k`, `φ k` sends every entry of the first matrix to the corresponding entry
of the `k`-th matrix. The approximation is preserved by `1`, `Matrix.single`, sums, differences
and products, hence by evaluating words in elementary matrices.
-/

namespace GroupApproximation.Full.SK04

open Filter

section Maps

variable {R : Type*} [Ring R] {M : ℕ → Type*} [∀ k, Ring (M k)] (φ : ∀ k, R → M k)

/-- An eventually additive map eventually sends `0` to `0`. -/
theorem eventually_map_zero
    (hadd : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r + r') = φ k r + φ k r') :
    ∀ᶠ k in atTop, φ k 0 = 0 := by
  filter_upwards [hadd 0 0] with k hk
  rw [add_zero] at hk
  exact left_eq_add.mp hk

/-- An eventually additive map eventually commutes with negation of a fixed element. -/
theorem eventually_map_neg
    (hadd : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r + r') = φ k r + φ k r') (a : R) :
    ∀ᶠ k in atTop, φ k (-a) = -φ k a := by
  filter_upwards [hadd a (-a), eventually_map_zero φ hadd] with k hk h0
  rw [add_neg_cancel a, h0] at hk
  exact (neg_eq_of_add_eq_zero_right hk.symm).symm

/-- An eventually additive map eventually commutes with a fixed difference. -/
theorem eventually_map_sub
    (hadd : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r + r') = φ k r + φ k r') (a b : R) :
    ∀ᶠ k in atTop, φ k (a - b) = φ k a - φ k b := by
  filter_upwards [hadd a (-b), eventually_map_neg φ hadd b] with k hk hn
  rw [sub_eq_add_neg a b, hk, hn, ← sub_eq_add_neg]

/-- An eventually additive map eventually commutes with a fixed finite sum. -/
theorem eventually_map_sum
    (hadd : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r + r') = φ k r + φ k r')
    {α : Type*} [DecidableEq α] (f : α → R) (s : Finset α) :
    ∀ᶠ k in atTop, φ k (∑ x ∈ s, f x) = ∑ x ∈ s, φ k (f x) := by
  refine Finset.induction_on s ?_ ?_
  · filter_upwards [eventually_map_zero φ hadd] with k hk
    rw [Finset.sum_empty, Finset.sum_empty, hk]
  · intro a s ha ih
    filter_upwards [ih, hadd (f a) (∑ x ∈ s, f x)] with k hk hk'
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hk', hk]

end Maps

section Entries

variable {R : Type*} [Ring R] {M : ℕ → Type*} [∀ k, Ring (M k)] (φ : ∀ k, R → M k)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The identity matrix is entrywise approximated by the identity matrices. -/
theorem eventually_entries_one
    (hadd : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r + r') = φ k r + φ k r')
    (h1 : ∀ k, φ k 1 = 1) :
    ∀ᶠ k in atTop, ∀ i j : ι,
      φ k ((1 : Matrix ι ι R) i j) = (1 : Matrix ι ι (M k)) i j := by
  filter_upwards [eventually_map_zero φ hadd] with k h0
  intro i j
  rw [Matrix.one_apply, Matrix.one_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h]
    exact h1 k
  · rw [if_neg h, if_neg h]
    exact h0

/-- A matrix unit with an approximated coefficient is entrywise approximated. -/
theorem eventually_entries_single
    (hadd : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r + r') = φ k r + φ k r')
    (i₀ j₀ : ι) (a : R) (a' : ∀ k, M k) (ha : ∀ᶠ k in atTop, φ k a = a' k) :
    ∀ᶠ k in atTop, ∀ i j : ι,
      φ k (Matrix.single i₀ j₀ a i j) = Matrix.single i₀ j₀ (a' k) i j := by
  filter_upwards [ha, eventually_map_zero φ hadd] with k hk h0
  intro i j
  rw [Matrix.single_apply, Matrix.single_apply]
  by_cases h : i₀ = i ∧ j₀ = j
  · rw [if_pos h, if_pos h]
    exact hk
  · rw [if_neg h, if_neg h]
    exact h0

/-- Entrywise approximation is preserved by sums. -/
theorem eventually_entries_add
    (hadd : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r + r') = φ k r + φ k r')
    (A B : Matrix ι ι R) (A' B' : ∀ k, Matrix ι ι (M k))
    (hA : ∀ᶠ k in atTop, ∀ i j : ι, φ k (A i j) = A' k i j)
    (hB : ∀ᶠ k in atTop, ∀ i j : ι, φ k (B i j) = B' k i j) :
    ∀ᶠ k in atTop, ∀ i j : ι, φ k ((A + B) i j) = (A' k + B' k) i j := by
  filter_upwards [hA, hB,
    Filter.eventually_all.2 fun i : ι => Filter.eventually_all.2 fun j : ι =>
      hadd (A i j) (B i j)]
    with k hAk hBk hk
  intro i j
  rw [Matrix.add_apply, Matrix.add_apply, hk i j, hAk i j, hBk i j]

/-- Entrywise approximation is preserved by differences. -/
theorem eventually_entries_sub
    (hadd : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r + r') = φ k r + φ k r')
    (A B : Matrix ι ι R) (A' B' : ∀ k, Matrix ι ι (M k))
    (hA : ∀ᶠ k in atTop, ∀ i j : ι, φ k (A i j) = A' k i j)
    (hB : ∀ᶠ k in atTop, ∀ i j : ι, φ k (B i j) = B' k i j) :
    ∀ᶠ k in atTop, ∀ i j : ι, φ k ((A - B) i j) = (A' k - B' k) i j := by
  filter_upwards [hA, hB,
    Filter.eventually_all.2 fun i : ι => Filter.eventually_all.2 fun j : ι =>
      eventually_map_sub φ hadd (A i j) (B i j)]
    with k hAk hBk hk
  intro i j
  rw [Matrix.sub_apply, Matrix.sub_apply, hk i j, hAk i j, hBk i j]

/-- Entrywise approximation is preserved by products: a product entry is a finite sum of
products of entries. -/
theorem eventually_entries_mul
    (hadd : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r + r') = φ k r + φ k r')
    (hmul : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r * r') = φ k r * φ k r')
    (A B : Matrix ι ι R) (A' B' : ∀ k, Matrix ι ι (M k))
    (hA : ∀ᶠ k in atTop, ∀ i j : ι, φ k (A i j) = A' k i j)
    (hB : ∀ᶠ k in atTop, ∀ i j : ι, φ k (B i j) = B' k i j) :
    ∀ᶠ k in atTop, ∀ i j : ι, φ k ((A * B) i j) = (A' k * B' k) i j := by
  filter_upwards [hA, hB,
    Filter.eventually_all.2 fun i : ι => Filter.eventually_all.2 fun j : ι =>
      eventually_map_sum φ hadd (fun l : ι => A i l * B l j) Finset.univ,
    Filter.eventually_all.2 fun i : ι => Filter.eventually_all.2 fun l : ι =>
      Filter.eventually_all.2 fun j : ι => hmul (A i l) (B l j)]
    with k hAk hBk hsum hprod
  intro i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  calc φ k (∑ l, A i l * B l j) = ∑ l, φ k (A i l * B l j) := hsum i j
    _ = ∑ l, A' k i l * B' k l j :=
      Finset.sum_congr rfl fun l _ => by rw [hprod i l j, hAk i l, hBk l j]

/-- The elementary matrix `x_{ij}(a)` is entrywise approximated by the matrices
`x_{ij}(φ_k(a))`. -/
theorem eventually_entries_elementaryUnit
    (hadd : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r + r') = φ k r + φ k r')
    (h1 : ∀ k, φ k 1 = 1) (i₀ j₀ : ι) (h : i₀ ≠ j₀) (a : R) :
    ∀ᶠ k in atTop, ∀ i j : ι,
      φ k (((elementaryUnit i₀ j₀ h a : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j) =
        ((elementaryUnit i₀ j₀ h (φ k a) : (Matrix ι ι (M k))ˣ) : Matrix ι ι (M k)) i j := by
  filter_upwards [eventually_entries_add (ι := ι) φ hadd 1 (Matrix.single i₀ j₀ a)
    (fun _ => 1) (fun k => Matrix.single i₀ j₀ (φ k a))
    (eventually_entries_one φ hadd h1)
    (eventually_entries_single φ hadd i₀ j₀ a (fun k => φ k a)
      (Filter.Eventually.of_forall fun _ => rfl))] with k hk
  exact hk

/-- The inverse `x_{ij}(-a) = I - a E_{ij}` of an elementary matrix is entrywise approximated by
the inverses of the matrices `x_{ij}(φ_k(a))`. -/
theorem eventually_entries_elementaryUnit_inv
    (hadd : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r + r') = φ k r + φ k r')
    (h1 : ∀ k, φ k 1 = 1) (i₀ j₀ : ι) (h : i₀ ≠ j₀) (a : R) :
    ∀ᶠ k in atTop, ∀ i j : ι,
      φ k ((((elementaryUnit i₀ j₀ h a)⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j) =
        (((elementaryUnit i₀ j₀ h (φ k a))⁻¹ : (Matrix ι ι (M k))ˣ) :
          Matrix ι ι (M k)) i j := by
  filter_upwards [eventually_entries_sub (ι := ι) φ hadd 1 (Matrix.single i₀ j₀ a)
    (fun _ => 1) (fun k => Matrix.single i₀ j₀ (φ k a))
    (eventually_entries_one φ hadd h1)
    (eventually_entries_single φ hadd i₀ j₀ a (fun k => φ k a)
      (Filter.Eventually.of_forall fun _ => rfl))] with k hk
  exact hk

/-- **Words are entrywise approximated.** If every marker and its inverse is entrywise
approximated, then so is the value of every word. -/
theorem eventually_entries_lift {α : Type*}
    (hadd : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r + r') = φ k r + φ k r')
    (hmul : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r * r') = φ k r * φ k r')
    (h1 : ∀ k, φ k 1 = 1)
    (t : α → (Matrix ι ι R)ˣ) (t' : ∀ k, α → (Matrix ι ι (M k))ˣ)
    (hval : ∀ x, ∀ᶠ k in atTop, ∀ i j : ι,
      φ k (((t x : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j) =
        ((t' k x : (Matrix ι ι (M k))ˣ) : Matrix ι ι (M k)) i j)
    (hinv : ∀ x, ∀ᶠ k in atTop, ∀ i j : ι,
      φ k ((((t x)⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j) =
        (((t' k x)⁻¹ : (Matrix ι ι (M k))ˣ) : Matrix ι ι (M k)) i j)
    (w : FreeGroup α) :
    ∀ᶠ k in atTop, ∀ i j : ι,
      φ k (((FreeGroup.lift t w : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j) =
        ((FreeGroup.lift (t' k) w : (Matrix ι ι (M k))ˣ) : Matrix ι ι (M k)) i j := by
  induction w using FreeGroup.induction_on with
  | C1 =>
    filter_upwards [eventually_entries_one (ι := ι) φ hadd h1] with k hk
    intro i j
    rw [map_one, map_one]
    exact hk i j
  | of x =>
    filter_upwards [hval x] with k hk
    intro i j
    rw [FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    exact hk i j
  | inv_of x _ =>
    filter_upwards [hinv x] with k hk
    intro i j
    rw [map_inv, map_inv, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    exact hk i j
  | mul x y hx hy =>
    filter_upwards [eventually_entries_mul φ hadd hmul
      ((FreeGroup.lift t x : (Matrix ι ι R)ˣ) : Matrix ι ι R)
      ((FreeGroup.lift t y : (Matrix ι ι R)ˣ) : Matrix ι ι R)
      (fun k => ((FreeGroup.lift (t' k) x : (Matrix ι ι (M k))ˣ) : Matrix ι ι (M k)))
      (fun k => ((FreeGroup.lift (t' k) y : (Matrix ι ι (M k))ˣ) : Matrix ι ι (M k)))
      hx hy] with k hk
    intro i j
    rw [map_mul, map_mul]
    exact hk i j

/-- **The forward half of the printed marked-limit argument** (tex l.317–342): a word that is
trivial in the source is eventually trivial in the approximating groups. -/
theorem eventually_lift_eq_one {α : Type*}
    (hadd : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r + r') = φ k r + φ k r')
    (hmul : ∀ r r' : R, ∀ᶠ k in atTop, φ k (r * r') = φ k r * φ k r')
    (h1 : ∀ k, φ k 1 = 1)
    (t : α → (Matrix ι ι R)ˣ) (t' : ∀ k, α → (Matrix ι ι (M k))ˣ)
    (hval : ∀ x, ∀ᶠ k in atTop, ∀ i j : ι,
      φ k (((t x : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j) =
        ((t' k x : (Matrix ι ι (M k))ˣ) : Matrix ι ι (M k)) i j)
    (hinv : ∀ x, ∀ᶠ k in atTop, ∀ i j : ι,
      φ k ((((t x)⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j) =
        (((t' k x)⁻¹ : (Matrix ι ι (M k))ˣ) : Matrix ι ι (M k)) i j)
    (w : FreeGroup α) (hw : FreeGroup.lift t w = 1) :
    ∀ᶠ k in atTop, FreeGroup.lift (t' k) w = 1 := by
  filter_upwards [eventually_entries_lift φ hadd hmul h1 t t' hval hinv w,
    eventually_entries_one (ι := ι) φ hadd h1] with k hk h1k
  apply Units.ext
  apply Matrix.ext
  intro i j
  rw [← hk i j, hw]
  exact h1k i j

end Entries

end GroupApproximation.Full.SK04
