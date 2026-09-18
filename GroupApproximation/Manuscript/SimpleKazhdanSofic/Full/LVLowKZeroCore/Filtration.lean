import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVLowKZeroCore.Grading
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The `s`-word filtration of `L_k(1,2)` and the constant term

Ingredient of `binaryLeavitt_idempotent_dichotomy` (manuscript
`simple_kazhdan_sofic_group.tex`, l.733-735, `sec:questions`, question Q2).

* `fil k n` is the `k`-span of the `s`-words of length `< n`.
* `pos k n` is the `k`-span of the nonempty `s`-words of length `< n`.
  Every element of `pos k n` has zero grading coefficient in each degree `≤ 0`.
* `constTerm k : L →ₗ[k] k` is a functional that sends `1` to `1` and every
  nonempty `s`-word to `0`.  It is built from the degree-zero coefficient of
  the grading.
* For `x ∈ fil k n`, the difference `x - constTerm k x • 1` lies in `pos k n`.
* `t_i` sends `pos k (n + 1)` into `fil k n`.
-/

namespace GroupApproximation.Full.LVLowKZeroCore

open GroupApproximation.BinaryLeavitt

noncomputable section

variable (k : Type) [Field k]

/-- The `s`-words of length `< n`. -/
def filSet (n : ℕ) : Set (BinaryLeavittAlgebra k) :=
  {x | ∃ a : List (Fin 2), a.length < n ∧ x = (family k).wordS a}

/-- The `k`-span of the `s`-words of length `< n`. -/
def fil (n : ℕ) : Submodule k (BinaryLeavittAlgebra k) :=
  Submodule.span k (filSet k n)

/-- The nonempty `s`-words of length `< n`. -/
def posSet (n : ℕ) : Set (BinaryLeavittAlgebra k) :=
  {x | ∃ (i : Fin 2) (a : List (Fin 2)), a.length + 1 < n ∧ x = (family k).wordS (i :: a)}

/-- The `k`-span of the nonempty `s`-words of length `< n`. -/
def pos (n : ℕ) : Submodule k (BinaryLeavittAlgebra k) :=
  Submodule.span k (posSet k n)

theorem wordS_mem_fil {n : ℕ} {a : List (Fin 2)} (ha : a.length < n) :
    (family k).wordS a ∈ fil k n :=
  Submodule.subset_span ⟨a, ha, rfl⟩

theorem fil_mono {m n : ℕ} (hmn : m ≤ n) : fil k m ≤ fil k n := by
  refine Submodule.span_mono ?_
  rintro x ⟨a, ha, rfl⟩
  exact ⟨a, lt_of_lt_of_le ha hmn, rfl⟩

theorem eq_zero_of_mem_fil_zero {x : BinaryLeavittAlgebra k} (hx : x ∈ fil k 0) : x = 0 := by
  have h : fil k 0 = ⊥ := by
    refine Submodule.span_eq_bot.mpr ?_
    rintro y ⟨a, ha, -⟩
    exact absurd ha (Nat.not_lt_zero _)
  rw [h] at hx
  exact (Submodule.mem_bot k).mp hx

/-- Elements of `pos k n` have vanishing grading coefficients in degrees `≤ 0`. -/
theorem coeff_grade_eq_zero_of_mem_pos {n : ℕ} {x : BinaryLeavittAlgebra k}
    (hx : x ∈ pos k n) (d : ℤ) (hd : d ≤ 0) : (grade k x).coeff d = 0 := by
  induction hx using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨i, a, -, rfl⟩ := hu
      rw [grade_wordS, AddMonoidAlgebra.coeff_single]
      refine Finsupp.single_eq_of_ne ?_
      rw [List.length_cons]
      omega
  | zero =>
      rw [map_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  | add v w _ _ hv hw =>
      rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hv, hw, add_zero]
  | smul c v _ hv =>
      rw [map_smul, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, hv, smul_zero]

theorem exists_dual_one :
    ∃ ψ : Module.Dual k (BinaryLeavittAlgebra k), ψ 1 = 1 :=
  Module.Projective.exists_dual_eq_one k (one_ne_zero : (1 : BinaryLeavittAlgebra k) ≠ 0)

/-- A functional sending `1` to `1` and nonempty `s`-words to `0`: a fixed
dual vector applied to the degree-zero grading coefficient. -/
def constTerm : BinaryLeavittAlgebra k →ₗ[k] k :=
  (Classical.choose (exists_dual_one k)) ∘ₗ coeffZero k

theorem constTerm_one : constTerm k 1 = 1 := by
  rw [constTerm, LinearMap.comp_apply, coeffZero_one]
  exact Classical.choose_spec (exists_dual_one k)

theorem constTerm_wordS_cons (i : Fin 2) (a : List (Fin 2)) :
    constTerm k ((family k).wordS (i :: a)) = 0 := by
  rw [constTerm, LinearMap.comp_apply, coeffZero_wordS_cons, map_zero]

/-- Removing the constant term moves `fil k n` into `pos k n`. -/
theorem sub_constTerm_mem_pos {n : ℕ} {x : BinaryLeavittAlgebra k} (hx : x ∈ fil k n) :
    x - constTerm k x • (1 : BinaryLeavittAlgebra k) ∈ pos k n := by
  induction hx using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨a, ha, rfl⟩ := hu
      cases a with
      | nil =>
          rw [LeavittFamily.wordS_nil, constTerm_one, one_smul, sub_self]
          exact Submodule.zero_mem _
      | cons i a =>
          rw [constTerm_wordS_cons, zero_smul, sub_zero]
          rw [List.length_cons] at ha
          exact Submodule.subset_span ⟨i, a, ha, rfl⟩
  | zero =>
      rw [map_zero, zero_smul, sub_zero]
      exact Submodule.zero_mem _
  | add v w _ _ hv hw =>
      have h : v + w - constTerm k (v + w) • (1 : BinaryLeavittAlgebra k) =
          (v - constTerm k v • (1 : BinaryLeavittAlgebra k)) +
            (w - constTerm k w • (1 : BinaryLeavittAlgebra k)) := by
        rw [map_add, add_smul]
        abel
      rw [h]
      exact Submodule.add_mem _ hv hw
  | smul c v _ hv =>
      have h : c • v - constTerm k (c • v) • (1 : BinaryLeavittAlgebra k) =
          c • (v - constTerm k v • (1 : BinaryLeavittAlgebra k)) := by
        rw [map_smul, smul_eq_mul, mul_smul, smul_sub]
      rw [h]
      exact Submodule.smul_mem _ c hv

/-- A deletion operator lowers the filtration: `t_i · pos k (n + 1) ⊆ fil k n`. -/
theorem t_mul_mem_fil {n : ℕ} {p : BinaryLeavittAlgebra k} (hp : p ∈ pos k (n + 1))
    (i : Fin 2) : (family k).t i * p ∈ fil k n := by
  induction hp using Submodule.span_induction with
  | mem u hu =>
      obtain ⟨j, a, ha, rfl⟩ := hu
      rw [LeavittFamily.wordS_cons, ← mul_assoc, LeavittFamily.t_mul_s]
      split_ifs
      · rw [one_mul]
        exact wordS_mem_fil k (by omega)
      · rw [zero_mul]
        exact Submodule.zero_mem _
  | zero =>
      rw [mul_zero]
      exact Submodule.zero_mem _
  | add v w _ _ hv hw =>
      rw [mul_add]
      exact Submodule.add_mem _ hv hw
  | smul c v _ hv =>
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ c hv

end

end GroupApproximation.Full.LVLowKZeroCore
