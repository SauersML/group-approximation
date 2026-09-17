import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Weyl.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Weyl conjugation of roots that meet `{i, j}` in at most one index (lane sk-leavitt-01)

Assume `2 = 0` in `R`.  Write `A = x_ij(1)` and `B = x_ji(1)`, so `w_ij = A B A` and conjugation by
`w_ij` is conjugation by `A`, then `B`, then `A` (`weyl_conj_via`).  Let `k, l` be indices
outside `{i, j}`.  The four one-index cases are three-step computations:

* `x_il(c)`: `A` fixes it, `B` gives `x_jl(c) x_il(c)`, `A` gives `x_il(c) x_jl(c) x_il(c) = x_jl(c)`.
* `x_jl(c)`: `A` gives `x_il(c) x_jl(c)`, `B` gives `x_jl(c) x_il(c) x_jl(c) = x_il(c)`, `A` fixes it.
* `x_ki(c)`: `A` gives `x_kj(c) x_ki(c)`, `B` gives `x_ki(c) x_kj(c) x_ki(c) = x_kj(c)`, `A` fixes it.
* `x_kj(c)`: `A` fixes it, `B` gives `x_ki(c) x_kj(c)`, `A` gives `x_kj(c) x_ki(c) x_kj(c) = x_ki(c)`.

Each last equality uses that roots in one row, or in one column, commute, together with
`x(c) x(c) = 1`.  If `{k, l}` misses `{i, j}`, then `A` and `B` commute with `x_kl(c)`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open scoped commutatorElement
open GroupApproximation.SteinbergGroup
open WeylCalc

variable {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]

/-- `w_ij x_kl(c) w_ij⁻¹ = x_kl(c)` when `{k, l} ∩ {i, j} = ∅` (any ring). -/
theorem weyl_conj_disjoint (i j k l : I) (hij : i ≠ j) (hkl : k ≠ l)
    (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i) (hlj : l ≠ j) (c : R) :
    weyl i j hij * x k l hkl c * (weyl i j hij)⁻¹ = x k l hkl c := by
  have hA : Commute (x i j hij (1 : R)) (x k l hkl c) :=
    x_commute_of_ne i j k l hij hkl hkj.symm hli 1 c
  have hB : Commute (x j i hij.symm (1 : R)) (x k l hkl c) :=
    x_commute_of_ne j i k l hij.symm hkl hki.symm hlj 1 c
  exact weyl_conj_via (conj_of_commute hA) (conj_of_commute hB) (conj_of_commute hA)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_conj_disjoint

/-- `w_ij x_il(c) w_ij⁻¹ = x_jl(c)` for `l ∉ {i, j}`, when `2 = 0`. -/
theorem weyl_conj_row_left (h2 : (2 : R) = 0) (i j l : I) (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) (c : R) :
    weyl i j hij * x i l hil c * (weyl i j hij)⁻¹ = x j l hjl c := by
  have hA : Commute (x i j hij (1 : R)) (x i l hil c) :=
    x_commute_of_ne i j i l hij hil hij.symm hil.symm 1 c
  have hC : Commute (x i l hil c) (x j l hjl c) :=
    x_commute_of_ne i l j l hil hjl hjl.symm hil.symm c c
  refine weyl_conj_via (h := x i l hil c) (k := x j l hjl (1 * c) * x i l hil c)
    (conj_of_commute hA) (conj_adj_left j i l hij.symm hil hjl 1 c) ?_
  calc x i j hij (1 : R) * (x j l hjl (1 * c) * x i l hil c) * (x i j hij (1 : R))⁻¹
      = (x i j hij (1 : R) * x j l hjl (1 * c) * (x i j hij (1 : R))⁻¹) *
          (x i j hij (1 : R) * x i l hil c * (x i j hij (1 : R))⁻¹) := by group
    _ = x i l hil (1 * (1 * c)) * x j l hjl (1 * c) * x i l hil c := by
        rw [conj_adj_left i j l hij hjl hil 1 (1 * c), conj_of_commute hA]
    _ = x j l hjl c * (x i l hil c * x i l hil c) := by
        simp only [one_mul]
        rw [hC.eq, mul_assoc]
    _ = x j l hjl c := by rw [x_mul_self h2, mul_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_conj_row_left

/-- `w_ij x_jl(c) w_ij⁻¹ = x_il(c)` for `l ∉ {i, j}`, when `2 = 0`. -/
theorem weyl_conj_row_right (h2 : (2 : R) = 0) (i j l : I) (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) (c : R) :
    weyl i j hij * x j l hjl c * (weyl i j hij)⁻¹ = x i l hil c := by
  have hA : Commute (x i j hij (1 : R)) (x i l hil c) :=
    x_commute_of_ne i j i l hij hil hij.symm hil.symm 1 c
  have hB : Commute (x j i hij.symm (1 : R)) (x j l hjl c) :=
    x_commute_of_ne j i j l hij.symm hjl hij hjl.symm 1 c
  have hC : Commute (x j l hjl c) (x i l hil c) :=
    x_commute_of_ne j l i l hjl hil hil.symm hjl.symm c c
  refine weyl_conj_via (h := x i l hil (1 * c) * x j l hjl c) (k := x i l hil c)
    (conj_adj_left i j l hij hjl hil 1 c) ?_ (conj_of_commute hA)
  calc x j i hij.symm (1 : R) * (x i l hil (1 * c) * x j l hjl c) *
        (x j i hij.symm (1 : R))⁻¹
      = (x j i hij.symm (1 : R) * x i l hil (1 * c) * (x j i hij.symm (1 : R))⁻¹) *
          (x j i hij.symm (1 : R) * x j l hjl c * (x j i hij.symm (1 : R))⁻¹) := by group
    _ = x j l hjl (1 * (1 * c)) * x i l hil (1 * c) * x j l hjl c := by
        rw [conj_adj_left j i l hij.symm hil hjl 1 (1 * c), conj_of_commute hB]
    _ = x i l hil c * (x j l hjl c * x j l hjl c) := by
        simp only [one_mul]
        rw [hC.eq, mul_assoc]
    _ = x i l hil c := by rw [x_mul_self h2, mul_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_conj_row_right

/-- `w_ij x_ki(c) w_ij⁻¹ = x_kj(c)` for `k ∉ {i, j}`, when `2 = 0`. -/
theorem weyl_conj_col_left (h2 : (2 : R) = 0) (i j k : I) (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) (c : R) :
    weyl i j hij * x k i hki c * (weyl i j hij)⁻¹ = x k j hkj c := by
  have hA : Commute (x i j hij (1 : R)) (x k j hkj c) :=
    x_commute_of_ne i j k j hij hkj hkj.symm hij.symm 1 c
  have hB : Commute (x j i hij.symm (1 : R)) (x k i hki c) :=
    x_commute_of_ne j i k i hij.symm hki hki.symm hij 1 c
  have hC : Commute (x k i hki c) (x k j hkj c) :=
    x_commute_of_ne k i k j hki hkj hki.symm hkj.symm c c
  refine weyl_conj_via (h := x k j hkj (c * 1) * x k i hki c) (k := x k j hkj c)
    (conj_adj_right_two h2 k i j hki hij hkj c 1) ?_ (conj_of_commute hA)
  calc x j i hij.symm (1 : R) * (x k j hkj (c * 1) * x k i hki c) *
        (x j i hij.symm (1 : R))⁻¹
      = (x j i hij.symm (1 : R) * x k j hkj (c * 1) * (x j i hij.symm (1 : R))⁻¹) *
          (x j i hij.symm (1 : R) * x k i hki c * (x j i hij.symm (1 : R))⁻¹) := by group
    _ = x k i hki (c * 1 * 1) * x k j hkj (c * 1) * x k i hki c := by
        rw [conj_adj_right_two h2 k j i hkj hij.symm hki (c * 1) 1, conj_of_commute hB]
    _ = x k j hkj c * (x k i hki c * x k i hki c) := by
        simp only [mul_one]
        rw [hC.eq, mul_assoc]
    _ = x k j hkj c := by rw [x_mul_self h2, mul_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_conj_col_left

/-- `w_ij x_kj(c) w_ij⁻¹ = x_ki(c)` for `k ∉ {i, j}`, when `2 = 0`. -/
theorem weyl_conj_col_right (h2 : (2 : R) = 0) (i j k : I) (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) (c : R) :
    weyl i j hij * x k j hkj c * (weyl i j hij)⁻¹ = x k i hki c := by
  have hA : Commute (x i j hij (1 : R)) (x k j hkj c) :=
    x_commute_of_ne i j k j hij hkj hkj.symm hij.symm 1 c
  have hC : Commute (x k j hkj c) (x k i hki c) :=
    x_commute_of_ne k j k i hkj hki hkj.symm hki.symm c c
  refine weyl_conj_via (h := x k j hkj c) (k := x k i hki (c * 1) * x k j hkj c)
    (conj_of_commute hA) (conj_adj_right_two h2 k j i hkj hij.symm hki c 1) ?_
  calc x i j hij (1 : R) * (x k i hki (c * 1) * x k j hkj c) * (x i j hij (1 : R))⁻¹
      = (x i j hij (1 : R) * x k i hki (c * 1) * (x i j hij (1 : R))⁻¹) *
          (x i j hij (1 : R) * x k j hkj c * (x i j hij (1 : R))⁻¹) := by group
    _ = x k j hkj (c * 1 * 1) * x k i hki (c * 1) * x k j hkj c := by
        rw [conj_adj_right_two h2 k i j hki hij hkj (c * 1) 1, conj_of_commute hA]
    _ = x k i hki c * (x k j hkj c * x k j hkj c) := by
        simp only [mul_one]
        rw [hC.eq, mul_assoc]
    _ = x k i hki c := by rw [x_mul_self h2, mul_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.weyl_conj_col_right

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
