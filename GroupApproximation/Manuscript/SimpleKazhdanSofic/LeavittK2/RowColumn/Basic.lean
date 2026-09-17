import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.VecProd
import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.Meta.AxiomGuard

/-!
# Column and row vectors in `St_{n+1}(R)` (lane sk-leavitt-02)

The new index is `Fin.last n`, because `stab` pads along `Fin.castSucc`.

* `colVec a = ∏ᵢ x_{castSucc i, last}(a i)` and `rowVec b = ∏ᵢ x_{last, castSucc i}(b i)`.
  In each product the factors commute pairwise (`x_commute_of_ne`), so both are `noncommProd`s.
* `colVec_add` and `rowVec_add` show that both maps are additive.
* `RowColumn/RootConj.lean` has `x_conj_colVec` and `x_conj_rowVec`: conjugation by one padded
  root `z = x_{ij}(c)`, where `i ≠ j < n`.

## Truth check (on paper)

`z x_{j,last}(t) z⁻¹ = ⁅z, x_{j,last}(t)⁆ x_{j,last}(t) = x_{i,last}(ct) x_{j,last}(t)`.  Also, `z`
commutes with `x_{k,last}` for `k ≠ j`.  So `colVec a ↦ colVec (a + c a_j e_i) =
colVec ((1 + c E_ij) a)`.

`⁅x_{last,i}(t), z⁆ = x_{last,j}(tc)`, so
`z x_{last,i}(t) z⁻¹ = x_{last,j}(-tc) x_{last,i}(t)`.  Also, `z` commutes with `x_{last,k}` for
`k ≠ i`.  So `rowVec b ↦ rowVec (b + b_i (-c) e_j) = rowVec (b (1 - c E_ij))`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open SteinbergGroup BooneHigman.SteinbergBasic RowColumn
open scoped Matrix commutatorElement

variable {n : ℕ} {R : Type*} [Ring R]

/-- The column root `x_{castSucc i, last}(s)`. -/
def colRoot (i : Fin n) (s : R) : St (n + 1) R :=
  x i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) s

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.colRoot

/-- The row root `x_{last, castSucc i}(s)`. -/
def rowRoot (i : Fin n) (s : R) : St (n + 1) R :=
  x (Fin.last n) i.castSucc (Fin.castSucc_ne_last i).symm s

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rowRoot

theorem colRoot_commute (i j : Fin n) (s t : R) : Commute (colRoot i s) (colRoot j t) :=
  x_commute_of_ne i.castSucc (Fin.last n) j.castSucc (Fin.last n) (Fin.castSucc_ne_last i)
    (Fin.castSucc_ne_last j) (Fin.castSucc_ne_last j).symm (Fin.castSucc_ne_last i).symm s t

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.colRoot_commute

theorem rowRoot_commute (i j : Fin n) (s t : R) : Commute (rowRoot i s) (rowRoot j t) :=
  x_commute_of_ne (Fin.last n) i.castSucc (Fin.last n) j.castSucc (Fin.castSucc_ne_last i).symm
    (Fin.castSucc_ne_last j).symm (Fin.castSucc_ne_last i) (Fin.castSucc_ne_last j) s t

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rowRoot_commute

theorem colRoot_add (i : Fin n) (s t : R) : colRoot i (s + t) = colRoot i s * colRoot i t :=
  (x_mul _ _ _ s t).symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.colRoot_add

theorem rowRoot_add (i : Fin n) (s t : R) : rowRoot i (s + t) = rowRoot i s * rowRoot i t :=
  (x_mul _ _ _ s t).symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rowRoot_add

theorem colRoot_zero (i : Fin n) : colRoot i (0 : R) = 1 :=
  x_zero _ _ _

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.colRoot_zero

theorem rowRoot_zero (i : Fin n) : rowRoot i (0 : R) = 1 :=
  x_zero _ _ _

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rowRoot_zero

/-- The column vector `∏ᵢ x_{castSucc i, last}(a i)` in `St_{n+1}(R)`. -/
def colVec (a : Fin n → R) : St (n + 1) R :=
  rootVecProd (colRoot (n := n) (R := R)) colRoot_commute a

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.colVec

/-- The row vector `∏ᵢ x_{last, castSucc i}(b i)` in `St_{n+1}(R)`. -/
def rowVec (b : Fin n → R) : St (n + 1) R :=
  rootVecProd (rowRoot (n := n) (R := R)) rowRoot_commute b

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rowVec

theorem colVec_add (a b : Fin n → R) : colVec (a + b) = colVec a * colVec b :=
  rootVecProd_add (colRoot (n := n) (R := R)) colRoot_commute colRoot_add a b

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.colVec_add

theorem rowVec_add (a b : Fin n → R) : rowVec (a + b) = rowVec a * rowVec b :=
  rootVecProd_add (rowRoot (n := n) (R := R)) rowRoot_commute rowRoot_add a b

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rowVec_add

theorem colVec_update_zero (i : Fin n) (s : R) :
    colVec (Function.update (0 : Fin n → R) i s) = colRoot i s :=
  rootVecProd_update_zero (colRoot (n := n) (R := R)) colRoot_commute colRoot_zero i s

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.colVec_update_zero

theorem rowVec_update_zero (i : Fin n) (s : R) :
    rowVec (Function.update (0 : Fin n → R) i s) = rowRoot i s :=
  rootVecProd_update_zero (rowRoot (n := n) (R := R)) rowRoot_commute rowRoot_zero i s

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rowVec_update_zero

theorem colVec_split (a : Fin n → R) (j : Fin n) :
    colVec a = colRoot j (a j) * colVec (Function.update a j 0) :=
  rootVecProd_split (colRoot (n := n) (R := R)) colRoot_commute colRoot_add
    colRoot_zero a j

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.colVec_split

theorem rowVec_split (b : Fin n → R) (j : Fin n) :
    rowVec b = rowRoot j (b j) * rowVec (Function.update b j 0) :=
  rootVecProd_split (rowRoot (n := n) (R := R)) rowRoot_commute rowRoot_add
    rowRoot_zero b j

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rowVec_split

theorem colVec_commute (y : St (n + 1) R) (a : Fin n → R)
    (h : ∀ i, Commute y (colRoot i (a i))) : Commute y (colVec a) :=
  rootVecProd_commute (colRoot (n := n) (R := R)) colRoot_commute y a h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.colVec_commute

theorem rowVec_commute (y : St (n + 1) R) (b : Fin n → R)
    (h : ∀ i, Commute y (rowRoot i (b i))) : Commute y (rowVec b) :=
  rootVecProd_commute (rowRoot (n := n) (R := R)) rowRoot_commute y b h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rowVec_commute

theorem colVec_zero : colVec (0 : Fin n → R) = 1 := by
  have h := colVec_add (0 : Fin n → R) 0
  rw [add_zero] at h
  exact mul_left_cancel (a := colVec (0 : Fin n → R)) (by rw [mul_one]; exact h.symm)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.colVec_zero

theorem rowVec_zero : rowVec (0 : Fin n → R) = 1 := by
  have h := rowVec_add (0 : Fin n → R) 0
  rw [add_zero] at h
  exact mul_left_cancel (a := rowVec (0 : Fin n → R)) (by rw [mul_one]; exact h.symm)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.rowVec_zero

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
