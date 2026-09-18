import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKAssemble
import GroupApproximation.BooneHigman.Metabelian.VdKDiagGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Van der Kallen row data from the relators touching one base index

Lane `bh-met-90p`.  `VdKRowData n R X` asks for row roots `Trow j a = x_{last,j}(a)` on the
free `P̃`-set `VdKΩ n R X`, subject to five relator families.  Here `vdkDiag_RowCore n R X o`
asks for the same data, but the four non-additivity families are only required when some index
involved equals a fixed base index `o`:

* `row_comm (j, l)` when `j = o ∨ l = o`;
* `row_act_comm (j; k, l)` when `j = o ∨ k = o ∨ l = o`;
* `row_act_commutator (j, k)` when `j = o ∨ k = o`;
* `col_row_commutator (i, k)` when `i = o ∨ k = o`.

The remaining relators are derived (`vdkDiag_RowCore.toRowData`), writing
`T_j(a) = ⁅T_o(a), x_{oj}(1)⁆` and using the Steinberg relations of `St_n(R)`:

1. `row_act_comm (j; k, l)`: `T_o(a)` and `x_{oj}(1)` both commute with `x_{kl}(b)`;
2. `row_comm (j, l)`: `T_j(a)` commutes with `T_o(b)` and with `x_{ol}(1)`;
3. `row_act_commutator (j, k)`: `x_{jk}(b) T_j(a) x_{jk}(b)⁻¹ = ⁅T_o(a), x_{ok}(-b) x_{oj}(1)⁆`
   `= T_k(-ab) T_j(a)` (`vdkDiag_commutator_conj_inv`);
4. `col_row_commutator (i, k)`: `x_{i,last}(a) T_k(b) x_{i,last}(a)⁻¹`
   `= ⁅x_{io}(ab) T_o(b), x_{ok}(1)⁆ = T_k(b) x_{ik}(ab)` (`vdkDiag_commutator_nested`).

So the relator families shrink from `O(n²)` / `O(n³)` instances to `O(n)` / `O(n²)`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

/-- Row data for van der Kallen's action whose non-additivity relators are only required when
they touch the base index `o`. -/
structure vdkDiag_RowCore (n : ℕ) (R : Type*) [Ring R] (X : Type*) (o : Fin n) where
  /-- The row root `x_{last,j}(a)`. -/
  Trow : Fin n → R → Equiv.Perm (VdKΩ n R X)
  /-- Additivity of the row roots. -/
  row_add : ∀ (j : Fin n) (a b : R), Trow j a * Trow j b = Trow j (a + b)
  /-- Distinct row roots commute, when one of them is the base row. -/
  row_comm : ∀ (j l : Fin n), j ≠ l → (j = o ∨ l = o) → ∀ a b : R,
    Trow j a * Trow l b = Trow l b * Trow j a
  /-- `x_{last,j}` commutes with `x_{kl}` when `j ≠ k`, when some index is the base. -/
  row_act_comm : ∀ (j k l : Fin n) (hkl : k ≠ l), j ≠ k → (j = o ∨ k = o ∨ l = o) →
    ∀ a b : R, Trow j a * vdkAct X (x k l hkl b) = vdkAct X (x k l hkl b) * Trow j a
  /-- `⁅x_{last,j}(a), x_{jk}(b)⁆ = x_{last,k}(ab)`, when `j` or `k` is the base. -/
  row_act_commutator : ∀ (j k : Fin n) (hjk : j ≠ k), (j = o ∨ k = o) → ∀ a b : R,
    ⁅Trow j a, vdkAct X (x j k hjk b)⁆ = Trow k (a * b)
  /-- `⁅x_{i,last}(a), x_{last,k}(b)⁆ = x_{ik}(ab)`, when `i` or `k` is the base. -/
  col_row_commutator : ∀ (i k : Fin n) (hik : i ≠ k), (i = o ∨ k = o) → ∀ a b : R,
    ⁅vdkCol X i a, Trow k b⁆ = vdkAct X (x i k hik (a * b))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkDiag_RowCore

namespace vdkDiag_RowCore

variable {R : Type*} [Ring R] {n : ℕ} {X : Type*}

/-- Full row data restricts to row data touching any base index. -/
def ofRowData (D : VdKRowData n R X) (o : Fin n) : vdkDiag_RowCore n R X o where
  Trow := D.Trow
  row_add := D.row_add
  row_comm := fun j l hjl _ => D.row_comm j l hjl
  row_act_comm := fun j k l hkl hjk _ => D.row_act_comm j k l hkl hjk
  row_act_commutator := fun j k hjk _ => D.row_act_commutator j k hjk
  col_row_commutator := fun i k hik _ => D.col_row_commutator i k hik

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkDiag_RowCore.ofRowData

variable {o : Fin n} (C : vdkDiag_RowCore n R X o)

/-- The row root at `0` is trivial. -/
theorem trow_zero (l : Fin n) : C.Trow l 0 = 1 := by
  have h := C.row_add l 0 0
  rw [add_zero] at h
  apply mul_left_cancel (a := C.Trow l 0)
  simpa only [mul_one] using h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkDiag_RowCore.trow_zero

/-- A row root is the commutator of the base row root with a root of `St_n(R)`. -/
theorem trow_eq_commutator (j : Fin n) (hoj : o ≠ j) (a : R) :
    ⁅C.Trow o a, vdkAct X (x o j hoj 1)⁆ = C.Trow j a := by
  rw [C.row_act_commutator o j hoj (Or.inl rfl) a 1, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkDiag_RowCore.trow_eq_commutator

/-- Derived relator (1): `x_{last,j}` commutes with `x_{kl}` whenever `j ≠ k`. -/
theorem row_act_comm_all (j k l : Fin n) (hkl : k ≠ l) (hjk : j ≠ k) (a b : R) :
    C.Trow j a * vdkAct X (x k l hkl b) = vdkAct X (x k l hkl b) * C.Trow j a := by
  by_cases h : j = o ∨ k = o ∨ l = o
  · exact C.row_act_comm j k l hkl hjk h a b
  simp only [not_or] at h
  obtain ⟨hjo, hko, hlo⟩ := h
  have hoj : o ≠ j := fun h => hjo h.symm
  have hok : o ≠ k := fun h => hko h.symm
  have h1 : Commute (C.Trow o a) (vdkAct X (x k l hkl b)) :=
    C.row_act_comm o k l hkl hok (Or.inl rfl) a b
  have h2 : Commute (vdkAct X (x o j hoj 1)) (vdkAct X (x k l hkl b)) :=
    (x_commute_of_ne o j k l hoj hkl hjk hlo 1 b).map (vdkAct X)
  have h3 := vdkDiag_commute_commutator h1.symm h2.symm
  rw [C.trow_eq_commutator j hoj a] at h3
  exact h3.symm.eq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkDiag_RowCore.row_act_comm_all

/-- Derived relator (2): distinct row roots commute. -/
theorem row_comm_all (j l : Fin n) (hjl : j ≠ l) (a b : R) :
    C.Trow j a * C.Trow l b = C.Trow l b * C.Trow j a := by
  by_cases h : j = o ∨ l = o
  · exact C.row_comm j l hjl h a b
  simp only [not_or] at h
  obtain ⟨hjo, hlo⟩ := h
  have hol : o ≠ l := fun h => hlo h.symm
  have h1 : Commute (C.Trow j a) (C.Trow o b) := C.row_comm j o hjo (Or.inr rfl) a b
  have h2 : Commute (C.Trow j a) (vdkAct X (x o l hol 1)) :=
    C.row_act_comm_all j o l hol hjo a 1
  have h3 := vdkDiag_commute_commutator h1 h2
  rw [C.trow_eq_commutator l hol b] at h3
  exact h3.eq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkDiag_RowCore.row_comm_all

/-- Derived relator (3): `⁅x_{last,j}(a), x_{jk}(b)⁆ = x_{last,k}(ab)`. -/
theorem row_act_commutator_all (j k : Fin n) (hjk : j ≠ k) (a b : R) :
    ⁅C.Trow j a, vdkAct X (x j k hjk b)⁆ = C.Trow k (a * b) := by
  by_cases h : j = o ∨ k = o
  · exact C.row_act_commutator j k hjk h a b
  simp only [not_or] at h
  obtain ⟨hjo, hko⟩ := h
  have hoj : o ≠ j := fun h => hjo h.symm
  have hok : o ≠ k := fun h => hko h.symm
  have hSD : Commute (C.Trow o a) (vdkAct X (x j k hjk b)) :=
    C.row_act_comm_all o j k hjk hoj a b
  have hx : ⁅x j k hjk b, x o j hoj 1⁆ = x o k hok (-b) := by
    rw [← commutatorElement_inv, x_commutator o j k hoj hjk hok 1 b, one_mul, x_neg]
  have hDT : ⁅vdkAct X (x j k hjk b), vdkAct X (x o j hoj 1)⁆ = vdkAct X (x o k hok (-b)) := by
    rw [← hx, map_commutatorElement]
  have hSP : ⁅C.Trow o a, vdkAct X (x o k hok (-b))⁆ = C.Trow k (a * -b) :=
    C.row_act_commutator o k hok (Or.inl rfl) a (-b)
  have hPE : Commute (vdkAct X (x o k hok (-b))) (C.Trow j a) :=
    (C.row_act_comm_all j o k hok hjo a (-b)).symm
  rw [vdkDiag_commutator_conj_inv (C.trow_eq_commutator j hoj a) hSD hDT hSP hPE]
  apply inv_eq_of_mul_eq_one_right
  rw [C.row_add, mul_neg, neg_add_cancel, C.trow_zero]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkDiag_RowCore.row_act_commutator_all

/-- Derived relator (4): `⁅x_{i,last}(a), x_{last,k}(b)⁆ = x_{ik}(ab)` for `i ≠ k`. -/
theorem col_row_all (i k : Fin n) (hik : i ≠ k) (a b : R) :
    ⁅vdkCol X i a, C.Trow k b⁆ = vdkAct X (x i k hik (a * b)) := by
  by_cases h : i = o ∨ k = o
  · exact C.col_row_commutator i k hik h a b
  simp only [not_or] at h
  obtain ⟨hio, hko⟩ := h
  have hok : o ≠ k := fun h => hko h.symm
  have hki : k ≠ i := fun h => hik h.symm
  have hCZ : Commute (vdkCol X i a) (vdkAct X (x o k hok 1)) :=
    vdkCol_mul_act_comm X i o k hok hki a 1
  have hCY : ⁅vdkCol X i a, C.Trow o b⁆ = vdkAct X (x i o hio (a * b)) :=
    C.col_row_commutator i o hio (Or.inr rfl) a b
  have hx := x_commutator i o k hio hok hik (a * b) 1
  rw [mul_one] at hx
  have hWZ : ⁅vdkAct X (x i o hio (a * b)), vdkAct X (x o k hok 1)⁆ =
      vdkAct X (x i k hik (a * b)) := by
    rw [← hx, map_commutatorElement]
  have hWE : Commute (vdkAct X (x i o hio (a * b))) (C.Trow k b) :=
    (C.row_act_comm_all k i o hio hki b (a * b)).symm
  have hVE : Commute (vdkAct X (x i k hik (a * b))) (C.Trow k b) :=
    (C.row_act_comm_all k i k hik hki b (a * b)).symm
  exact vdkDiag_commutator_nested (C.trow_eq_commutator k hok b) hCZ hCY hWZ hWE hVE

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkDiag_RowCore.col_row_all

/-- Row data touching the base index extends to full row data. -/
def toRowData : VdKRowData n R X where
  Trow := C.Trow
  row_add := C.row_add
  row_comm := C.row_comm_all
  row_act_comm := C.row_act_comm_all
  row_act_commutator := C.row_act_commutator_all
  col_row_commutator := C.col_row_all

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkDiag_RowCore.toRowData

end vdkDiag_RowCore

end GroupApproximation.BooneHigman.Metabelian.ElemFP
