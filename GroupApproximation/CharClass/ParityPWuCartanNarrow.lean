import GroupApproximation.CharClass.ParityPWuCartan
import GroupApproximation.Meta.AxiomGuard

/-!
# The Cartan half of the diagonal Wu relation, from narrowed hypotheses

Lane `lx-splitK` (owner of `ParityP*`), ruling of `lx-design` 2026-09-12.

`ParityP.PowerData` asks for `P⁰ = id` and the Cartan formula on the whole ring `A`.  The
odd-primary operations cannot supply `P⁰ = id` on every class: that is a statement about universal
examples, and the tree has none.  The computation of `P^i(e_{i+1}(y))` only ever applies them
to the roots, to `1`, and to products of roots.  `PowerDataN` asks for exactly that.

* `P⁰` is asked on the roots and on `1` only (`p_zero_y`, `p_zero_one`).  `P⁰` of a product of
  roots follows from the Cartan formula at `n = 0` (`p_zero_prod`).
* `Pⁿ 1 = 0` for `n > 0` is a field (`p_one_pos`).  It is instability in degree `0`.
* The Cartan formula is asked for a root times a product of roots (`cartan_y`).

The results are those of `ParityPWuCartan`, with the same statements over `PowerDataN`.

## Main results

* `ParityP.PowerDataN` — the narrowed hypotheses.
* `ParityP.PowerDataN.p_zero_prod`, `p_mul_y`, `p_prod`.
* `ParityP.PowerDataN.p_gamma_succ_eq_smul` — `P^i(γ_{i+1}) = κ^i · m_{(p^i,1)}(y)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GroupApproximation.CharClass

namespace ParityP

/-- **The narrowed reduced-power data.**  A commutative ring with additive operations `P`, a
finite family of roots `y`, `P⁰ = id` on the roots and on `1`, `Pⁿ 1 = 0` for `n > 0`, the Cartan
formula for a root times a product of roots, and `P¹ y = κ·y^p`, `P^{≥2} y = 0` on the roots. -/
structure PowerDataN (σ : Type*) (A : Type*) [CommRing A] (p : ℕ) where
  /-- The reduced powers, additive in the class. -/
  P : ℕ → A →+ A
  /-- The index set of the Chern roots. -/
  s : Finset σ
  /-- The Chern roots, of cohomological degree two. -/
  y : σ → A
  /-- The normalisation constant of `P¹ y = κ·y^p`. -/
  κ : A
  /-- `P⁰` fixes every root. -/
  p_zero_y : ∀ k : σ, P 0 (y k) = y k
  /-- `P⁰ 1 = 1`. -/
  p_zero_one : P 0 1 = 1
  /-- `Pⁿ 1 = 0` for `n > 0` (instability in degree zero). -/
  p_one_pos : ∀ n : ℕ, 0 < n → P n 1 = 0
  /-- The Cartan formula for a root times a product of roots. -/
  cartan_y : ∀ (n : ℕ) (k : σ) (C : Finset σ),
    P n (y k * ∏ l ∈ C, y l)
      = ∑ j ∈ Finset.range (n + 1), P j (y k) * P (n - j) (∏ l ∈ C, y l)
  /-- `P¹` on a root is `κ` times its `p`-th power. -/
  p_y_one : ∀ k : σ, P 1 (y k) = κ * y k ^ p
  /-- Instability on a root: `P^j` vanishes for `j ≥ 2`. -/
  p_y_high : ∀ (k : σ) (j : ℕ), 2 ≤ j → P j (y k) = 0

namespace PowerDataN

variable {σ A : Type*} [CommRing A] {p : ℕ} (D : PowerDataN σ A p)

/-- `P` shifted down by one. -/
def pShift : ℕ → A → A
  | 0, _ => 0
  | (n + 1), u => D.P n u

@[simp] theorem pShift_zero (u : A) : D.pShift 0 u = 0 := rfl

@[simp] theorem pShift_succ (n : ℕ) (u : A) : D.pShift (n + 1) u = D.P n u := rfl

/-- **`P⁰` fixes every product of roots**, from `P⁰` on the roots and on `1` and the Cartan formula
at `n = 0`. -/
theorem p_zero_prod [DecidableEq σ] (C : Finset σ) :
    D.P 0 (∏ l ∈ C, D.y l) = ∏ l ∈ C, D.y l := by
  refine Finset.induction_on C ?_ ?_
  · rw [Finset.prod_empty, D.p_zero_one]
  · intro w C hw ih
    rw [Finset.prod_insert hw, D.cartan_y 0 w C, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, Nat.sub_zero, D.p_zero_y, ih]

/-- The Cartan formula against a root collapses to two terms, on a product of roots. -/
theorem p_mul_y (k : σ) (C : Finset σ) (n : ℕ) :
    D.P n (D.y k * ∏ l ∈ C, D.y l)
      = D.y k * D.P n (∏ l ∈ C, D.y l)
        + D.κ * D.y k ^ p * D.pShift n (∏ l ∈ C, D.y l) := by
  cases n with
  | zero =>
    show D.P 0 (D.y k * ∏ l ∈ C, D.y l)
        = D.y k * D.P 0 (∏ l ∈ C, D.y l) + D.κ * D.y k ^ p * D.pShift 0 (∏ l ∈ C, D.y l)
    rw [D.cartan_y 0 k C, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero,
      D.p_zero_y, pShift_zero, mul_zero, add_zero]
  | succ n =>
    show D.P (n + 1) (D.y k * ∏ l ∈ C, D.y l)
        = D.y k * D.P (n + 1) (∏ l ∈ C, D.y l)
          + D.κ * D.y k ^ p * D.pShift (n + 1) (∏ l ∈ C, D.y l)
    rw [D.cartan_y (n + 1) k C]
    have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (n + 1 + 1) := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      simp only [Finset.mem_range]
      rcases hj with rfl | rfl <;> omega
    have hzero : ∀ j ∈ Finset.range (n + 1 + 1), j ∉ ({0, 1} : Finset ℕ) →
        D.P j (D.y k) * D.P (n + 1 - j) (∏ l ∈ C, D.y l) = 0 := by
      intro j _ hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      have hzj : D.P j (D.y k) = 0 := by
        rcases j with _ | j
        · exact absurd rfl hj.1
        · rcases j with _ | j
          · exact absurd rfl hj.2
          · exact D.p_y_high k _ (by omega)
      rw [hzj, zero_mul]
    rw [← Finset.sum_subset hsub hzero, Finset.sum_pair (by omega : (0 : ℕ) ≠ 1),
      Nat.sub_zero, Nat.add_sub_cancel, D.p_zero_y, D.p_y_one, pShift_succ]

/-- **`P^c` of a squarefree monomial** raises exactly `c` of its factors to the `p`-th power, each
contributing a factor `κ`. -/
theorem p_prod [DecidableEq σ] (C : Finset σ) :
    ∀ c : ℕ, D.P c (∏ l ∈ C, D.y l)
      = wuMonomialP C (fun l => D.κ * D.y l ^ p) D.y c := by
  refine Finset.induction_on C ?_ ?_
  · intro c
    rw [Finset.prod_empty]
    cases c with
    | zero =>
      show D.P 0 (1 : A) = wuMonomialP (∅ : Finset σ) _ D.y 0
      rw [D.p_zero_one, wuMonomialP_zero, Finset.prod_empty]
    | succ c =>
      show D.P (c + 1) (1 : A) = wuMonomialP (∅ : Finset σ) _ D.y (c + 1)
      rw [D.p_one_pos (c + 1) (by omega),
        wuMonomialP_empty_of_pos _ D.y (show 0 < c + 1 by omega)]
  · intro w C hw ih c
    cases c with
    | zero =>
      show D.P 0 (∏ l ∈ insert w C, D.y l) = wuMonomialP (insert w C) _ D.y 0
      rw [D.p_zero_prod, wuMonomialP_zero]
    | succ c =>
      show D.P (c + 1) (∏ l ∈ insert w C, D.y l) = wuMonomialP (insert w C) _ D.y (c + 1)
      rw [Finset.prod_insert hw, D.p_mul_y, pShift_succ, ih (c + 1), ih c,
        wuMonomialP_insert hw]

/-- The `j`-th Chern class of the split family. -/
def gamma (j : ℕ) : A := esymmOn D.s D.y j

theorem gamma_def (j : ℕ) : D.gamma j = esymmOn D.s D.y j := rfl

@[simp] theorem gamma_zero : D.gamma 0 = 1 := esymmOn_zero _ _

/-- `P^i` of the `(i+1)`-st Chern class, as a sum over subsets. -/
theorem p_gamma_succ [DecidableEq σ] (i : ℕ) :
    D.P i (D.gamma (i + 1))
      = ∑ C ∈ D.s.powersetCard (i + 1), wuMonomialP C (fun l => D.κ * D.y l ^ p) D.y i := by
  rw [gamma_def, esymmOn_def, map_sum]
  exact Finset.sum_congr rfl fun C _ => D.p_prod C i

/-- **The Cartan half of L4a, narrowed.**  `P^i(γ_{i+1}) = κ^i · m_{(p^i,1)}(y)`. -/
theorem p_gamma_succ_eq_smul [DecidableEq σ] (i : ℕ) :
    D.P i (D.gamma (i + 1)) = D.κ ^ i * wuRHSP D.s (fun l => D.y l ^ p) D.y i := by
  rw [D.p_gamma_succ i, ← wuRHSP_eq_sum_wuMonomialP, wuRHSP_def, wuRHSP_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun B hB => ?_
  have hcard : B.card = i := (Finset.mem_powersetCard.mp hB).2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
  ring

end PowerDataN

end ParityP

#audit_axioms ParityP.PowerDataN
#audit_axioms ParityP.PowerDataN.p_zero_prod
#audit_axioms ParityP.PowerDataN.p_mul_y
#audit_axioms ParityP.PowerDataN.p_prod
#audit_axioms ParityP.PowerDataN.p_gamma_succ
#audit_axioms ParityP.PowerDataN.p_gamma_succ_eq_smul

end GroupApproximation.CharClass
