import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKParabolic
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2StabDiagAction
import GroupApproximation.Meta.AxiomGuard

/-!
# Assembling van der Kallen's action from row data

Lane `bh-met-50`.  `ElemFPK2VdKParabolic` builds the free `P̃`-set `VdKΩ n R X`.  It also gives
permutations for the roots of `St_n(R)` (`vdkAct`) and for the column roots `x_{i,last}`
(`vdkCol`), and proves every relator among them.  This module adds the row roots.

* `VdKRowData n R X` holds permutations `Trow j a` for the row roots `x_{last,j}(a)`.  It also
  holds the Steinberg relators that involve a row root:
  * `row_add`: additivity;
  * `row_comm`: distinct row roots commute;
  * `row_act_comm`: `x_{last,j}` commutes with `x_{kl}` when `j ≠ k`;
  * `row_act_commutator`: `⁅x_{last,j}(a), x_{jk}(b)⁆ = x_{last,k}(ab)`;
  * `col_row_commutator`: `⁅x_{i,last}(a), x_{last,k}(b)⁆ = x_{ik}(ab)` for `i ≠ k`.
* `VdKRowData.vdkT`: case analysis on whether each index is last.  It assigns `Trow`,
  `vdkCol`, `vdkAct ∘ x` or `1`.
* `VdKRowData.toLastRootAction`: the resulting `LastRootAction n R (VdKΩ n R X)`, with `act =
  vdkAct X`.  The relators with only column and `St_n` roots come from `ElemFPK2VdKParabolic`.
  The rest are the fields of `VdKRowData`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

/-- Permutations for the row roots `x_{last,j}` of `St_{n+1}(R)` on the free `P̃`-set, together
with the Steinberg relators that involve a row root. -/
structure VdKRowData (n : ℕ) (R : Type*) [Ring R] (X : Type*) where
  /-- The row root `x_{last,j}(a)`. -/
  Trow : Fin n → R → Equiv.Perm (VdKΩ n R X)
  /-- Additivity of the row roots. -/
  row_add : ∀ (j : Fin n) (a b : R), Trow j a * Trow j b = Trow j (a + b)
  /-- Distinct row roots commute. -/
  row_comm : ∀ (j l : Fin n), j ≠ l → ∀ a b : R, Trow j a * Trow l b = Trow l b * Trow j a
  /-- `x_{last,j}` commutes with `x_{kl}` when `j ≠ k`. -/
  row_act_comm : ∀ (j k l : Fin n) (hkl : k ≠ l), j ≠ k → ∀ a b : R,
    Trow j a * vdkAct X (x k l hkl b) = vdkAct X (x k l hkl b) * Trow j a
  /-- `⁅x_{last,j}(a), x_{jk}(b)⁆ = x_{last,k}(ab)`. -/
  row_act_commutator : ∀ (j k : Fin n) (hjk : j ≠ k) (a b : R),
    ⁅Trow j a, vdkAct X (x j k hjk b)⁆ = Trow k (a * b)
  /-- `⁅x_{i,last}(a), x_{last,k}(b)⁆ = x_{ik}(ab)` for `i ≠ k`. -/
  col_row_commutator : ∀ (i k : Fin n) (hik : i ≠ k) (a b : R),
    ⁅vdkCol X i a, Trow k b⁆ = vdkAct X (x i k hik (a * b))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowData

namespace VdKRowData

variable {R : Type*} [Ring R] {n : ℕ} {X : Type*} (D : VdKRowData n R X)

/-- All row roots commute, including two roots with the same index. -/
theorem row_mul_comm_all (j l : Fin n) (a b : R) :
    D.Trow j a * D.Trow l b = D.Trow l b * D.Trow j a := by
  by_cases h : j = l
  · subst h
    rw [D.row_add, D.row_add, add_comm]
  · exact D.row_comm j l h a b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowData.row_mul_comm_all

/-- The candidate permutation for the root `x_{ij}(a)` of `St_{n+1}(R)`. -/
def vdkT (i j : Fin (n + 1)) (a : R) : Equiv.Perm (VdKΩ n R X) :=
  Fin.lastCases (motive := fun _ => Equiv.Perm (VdKΩ n R X))
    (Fin.lastCases (motive := fun _ => Equiv.Perm (VdKΩ n R X)) 1 (fun j' => D.Trow j' a) j)
    (fun i' => Fin.lastCases (motive := fun _ => Equiv.Perm (VdKΩ n R X)) (vdkCol X i' a)
      (fun j' => if h : i' = j' then 1 else vdkAct X (x i' j' h a)) j) i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowData.vdkT

theorem vdkT_last_castSucc (j : Fin n) (a : R) :
    D.vdkT (Fin.last n) j.castSucc a = D.Trow j a := by
  simp only [vdkT, Fin.lastCases_last, Fin.lastCases_castSucc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowData.vdkT_last_castSucc

theorem vdkT_castSucc_last (i : Fin n) (a : R) :
    D.vdkT i.castSucc (Fin.last n) a = vdkCol X i a := by
  simp only [vdkT, Fin.lastCases_last, Fin.lastCases_castSucc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowData.vdkT_castSucc_last

theorem vdkT_castSucc_castSucc_of_ne (i j : Fin n) (hij : i ≠ j) (a : R) :
    D.vdkT i.castSucc j.castSucc a = vdkAct X (x i j hij a) := by
  simp only [vdkT, Fin.lastCases_castSucc, dif_neg hij]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowData.vdkT_castSucc_castSucc_of_ne

/-- Additivity of `vdkT` for roots with a last index. -/
theorem vdkT_add (i j : Fin (n + 1)) (hij : i ≠ j) (a b : R)
    (hL : i = Fin.last n ∨ j = Fin.last n) : D.vdkT i j a * D.vdkT i j b = D.vdkT i j (a + b) := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rcases hL with h | h <;> exact absurd h (Fin.castSucc_ne_last _)
  · simp only [vdkT_castSucc_last]
    exact vdkCol_add X i' a b
  · simp only [vdkT_last_castSucc]
    exact D.row_add j' a b
  · exact (hij rfl).elim

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowData.vdkT_add

/-- Commutation of non-addable roots for `vdkT`, when some index is last. -/
theorem vdkT_commute (i j k l : Fin (n + 1)) (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (a b : R)
    (hL : i = Fin.last n ∨ j = Fin.last n ∨ k = Fin.last n ∨ l = Fin.last n) :
    ⁅D.vdkT i j a, D.vdkT k l b⁆ = 1 := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last l with ⟨l', rfl⟩ | rfl
  · rcases hL with h | h | h | h <;> exact absurd h (Fin.castSucc_ne_last _)
  · rw [D.vdkT_castSucc_castSucc_of_ne i' j' (ne_of_apply_ne Fin.castSucc hij) a,
      D.vdkT_castSucc_last k' b]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (vdkCol_mul_act_comm X k' i' j' (ne_of_apply_ne Fin.castSucc hij)
        (ne_of_apply_ne Fin.castSucc hjk) b a).symm
  · rw [D.vdkT_castSucc_castSucc_of_ne i' j' (ne_of_apply_ne Fin.castSucc hij) a,
      D.vdkT_last_castSucc l' b]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (D.row_act_comm l' i' j' (ne_of_apply_ne Fin.castSucc hij)
        (ne_of_apply_ne Fin.castSucc hli) b a).symm
  · exact (hkl rfl).elim
  · rw [D.vdkT_castSucc_last i' a,
      D.vdkT_castSucc_castSucc_of_ne k' l' (ne_of_apply_ne Fin.castSucc hkl) b]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (vdkCol_mul_act_comm X i' k' l' (ne_of_apply_ne Fin.castSucc hkl)
        (ne_of_apply_ne Fin.castSucc hli) a b)
  · rw [D.vdkT_castSucc_last i' a, D.vdkT_castSucc_last k' b]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (vdkCol_mul_comm X i' k' a b)
  · exact (hjk rfl).elim
  · exact (hkl rfl).elim
  · rw [D.vdkT_last_castSucc j' a,
      D.vdkT_castSucc_castSucc_of_ne k' l' (ne_of_apply_ne Fin.castSucc hkl) b]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (D.row_act_comm j' k' l' (ne_of_apply_ne Fin.castSucc hkl)
        (ne_of_apply_ne Fin.castSucc hjk) a b)
  · exact (hli rfl).elim
  · rw [D.vdkT_last_castSucc j' a, D.vdkT_last_castSucc l' b]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (D.row_mul_comm_all j' l' a b)
  · exact (hkl rfl).elim
  all_goals exact (hij rfl).elim

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowData.vdkT_commute

/-- The adjacent commutator relation for `vdkT`, when some index is last. -/
theorem vdkT_adjacent (i j k : Fin (n + 1)) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R)
    (hL : i = Fin.last n ∨ j = Fin.last n ∨ k = Fin.last n) :
    ⁅D.vdkT i j a, D.vdkT j k b⁆ = D.vdkT i k (a * b) := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
  · rcases hL with h | h | h <;> exact absurd h (Fin.castSucc_ne_last _)
  · rw [D.vdkT_castSucc_castSucc_of_ne i' j' (ne_of_apply_ne Fin.castSucc hij) a,
      D.vdkT_castSucc_last j' b, D.vdkT_castSucc_last i' (a * b)]
    exact vdkAct_col_commutator X i' j' (ne_of_apply_ne Fin.castSucc hij) a b
  · rw [D.vdkT_castSucc_last i' a, D.vdkT_last_castSucc k' b,
      D.vdkT_castSucc_castSucc_of_ne i' k' (ne_of_apply_ne Fin.castSucc hik) (a * b)]
    exact D.col_row_commutator i' k' (ne_of_apply_ne Fin.castSucc hik) a b
  · exact (hjk rfl).elim
  · rw [D.vdkT_last_castSucc j' a,
      D.vdkT_castSucc_castSucc_of_ne j' k' (ne_of_apply_ne Fin.castSucc hjk) b,
      D.vdkT_last_castSucc k' (a * b)]
    exact D.row_act_commutator j' k' (ne_of_apply_ne Fin.castSucc hjk) a b
  · exact (hik rfl).elim
  all_goals exact (hij rfl).elim

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowData.vdkT_adjacent

/-- Van der Kallen's action assembled from row data: a `LastRootAction` on the free `P̃`-set,
whose action of `St_n(R)` is `vdkAct X`. -/
def toLastRootAction : LastRootAction n R (VdKΩ n R X) where
  act := vdkAct X
  T i j _ a := D.vdkT i j a
  compat i j hij _ a := D.vdkT_castSucc_castSucc_of_ne i j hij a
  add := D.vdkT_add
  commute := D.vdkT_commute
  adjacent := D.vdkT_adjacent

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowData.toLastRootAction

theorem toLastRootAction_act : D.toLastRootAction.act = vdkAct X :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowData.toLastRootAction_act

end VdKRowData

end GroupApproximation.BooneHigman.Metabelian.ElemFP
