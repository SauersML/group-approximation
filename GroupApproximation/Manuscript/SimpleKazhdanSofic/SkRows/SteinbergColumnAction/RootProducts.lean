import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.PaddedCentrality.Reduction
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Data.Matrix.Mul
import GroupApproximation.Meta.AxiomGuard

/-!
# Products of boundary roots indexed by vectors

Lane `sk-rows-13` (column/row action of `St_m(R)` on the last column and row of `St_{m+1}(R)`).
No single tex sentence is formalized here.  This module is infrastructure for the proof of
`PaddedCentrality.SteinbergColumnActionStatement` (lane `sk-rows-14`'s interface).

## Route

* The last-column roots `x_{k, m+1}(a)` pairwise commute for all `k, l : Fin m`
  (`SteinbergGroup.x_commute_of_ne`), and so do the last-row roots.
* `MonoidHom.noncommPiCoprod` packages them as monoid homs `(Fin m → Multiplicative R) →*
  St_{m+1}(R)`.  For a vector `v : Fin m → R` this defines `colProd v = ∏_k x_{k, m+1}(v k)` and
  `rowProd v = ∏_k x_{m+1, k}(v k)`, which are additive in `v`.
* `colProd (Pi.single i a) = x_{i, m+1}(a)`, and `colProd v` equals the `List.prod` over
  `List.finRange m` used in the interface.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality
open scoped Matrix

section Homs

variable (m : ℕ) (R : Type*) [Ring R]

/-- Any two last-column roots commute. -/
theorem colRoot_commute (k l : Fin m) (a b : R) :
    Commute (colRoot m R k a) (colRoot m R l b) :=
  SteinbergGroup.x_commute_of_ne k.castSucc (Fin.last m) l.castSucc (Fin.last m)
    (Fin.castSucc_ne_last k) (Fin.castSucc_ne_last l) (Fin.castSucc_ne_last l).symm
    (Fin.castSucc_ne_last k).symm a b

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.colRoot_commute

/-- Any two last-row roots commute. -/
theorem rowRoot_commute (k l : Fin m) (a b : R) :
    Commute (rowRoot m R k a) (rowRoot m R l b) :=
  SteinbergGroup.x_commute_of_ne (Fin.last m) k.castSucc (Fin.last m) l.castSucc
    (Fin.castSucc_ne_last k).symm (Fin.castSucc_ne_last l).symm (Fin.castSucc_ne_last k)
    (Fin.castSucc_ne_last l) a b

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.rowRoot_commute

/-- The last-column root group `x_{k, m+1}(·)` as a monoid hom. -/
def colRootHom (k : Fin m) : Multiplicative R →* St (m + 1) R where
  toFun a := colRoot m R k (Multiplicative.toAdd a)
  map_one' := by
    simp only [toAdd_one, colRoot_zero]
  map_mul' a b := by
    simp only [toAdd_mul, colRoot, SteinbergGroup.x_mul]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.colRootHom

/-- The last-row root group `x_{m+1, k}(·)` as a monoid hom. -/
def rowRootHom (k : Fin m) : Multiplicative R →* St (m + 1) R where
  toFun a := rowRoot m R k (Multiplicative.toAdd a)
  map_one' := by
    simp only [toAdd_one, rowRoot_zero]
  map_mul' a b := by
    simp only [toAdd_mul, rowRoot, SteinbergGroup.x_mul]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.rowRootHom

theorem colRootHom_commute :
    Pairwise fun k l : Fin m => ∀ a b : Multiplicative R,
      Commute (colRootHom m R k a) (colRootHom m R l b) :=
  fun k l _ a b => colRoot_commute m R k l (Multiplicative.toAdd a) (Multiplicative.toAdd b)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.colRootHom_commute

theorem rowRootHom_commute :
    Pairwise fun k l : Fin m => ∀ a b : Multiplicative R,
      Commute (rowRootHom m R k a) (rowRootHom m R l b) :=
  fun k l _ a b => rowRoot_commute m R k l (Multiplicative.toAdd a) (Multiplicative.toAdd b)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.rowRootHom_commute

/-- `v ↦ ∏_k x_{k, m+1}(v k)` as a monoid hom out of `(Multiplicative R)^m`. -/
def colHom : (Fin m → Multiplicative R) →* St (m + 1) R :=
  MonoidHom.noncommPiCoprod (colRootHom m R) (colRootHom_commute m R)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.colHom

/-- `v ↦ ∏_k x_{m+1, k}(v k)` as a monoid hom out of `(Multiplicative R)^m`. -/
def rowHom : (Fin m → Multiplicative R) →* St (m + 1) R :=
  MonoidHom.noncommPiCoprod (rowRootHom m R) (rowRootHom_commute m R)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.rowHom

end Homs

variable {m : ℕ} {R : Type*} [Ring R]

/-- The column product `∏_k x_{k, m+1}(v k)`. -/
def colProd (v : Fin m → R) : St (m + 1) R :=
  colHom m R fun k => Multiplicative.ofAdd (v k)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.colProd

/-- The row product `∏_k x_{m+1, k}(v k)`. -/
def rowProd (v : Fin m → R) : St (m + 1) R :=
  rowHom m R fun k => Multiplicative.ofAdd (v k)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.rowProd

theorem ofAdd_zero_fun :
    (fun k => Multiplicative.ofAdd ((0 : Fin m → R) k)) = 1 := by
  funext k
  simp only [Pi.zero_apply, ofAdd_zero, Pi.one_apply]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.ofAdd_zero_fun

theorem ofAdd_add_fun (v w : Fin m → R) :
    (fun k => Multiplicative.ofAdd ((v + w) k)) =
      (fun k => Multiplicative.ofAdd (v k)) * (fun k => Multiplicative.ofAdd (w k)) := by
  funext k
  simp only [Pi.add_apply, ofAdd_add, Pi.mul_apply]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.ofAdd_add_fun

theorem ofAdd_single (i : Fin m) (a : R) :
    (fun k => Multiplicative.ofAdd ((Pi.single i a : Fin m → R) k)) =
      Pi.mulSingle i (Multiplicative.ofAdd a) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [Pi.single_eq_same, Pi.mulSingle_eq_same]
  · simp only [Pi.single_eq_of_ne hk, Pi.mulSingle_eq_of_ne hk, ofAdd_zero]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.ofAdd_single

theorem colProd_zero : colProd (0 : Fin m → R) = 1 :=
  (congrArg (colHom m R) ofAdd_zero_fun).trans (map_one (colHom m R))

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.colProd_zero

theorem rowProd_zero : rowProd (0 : Fin m → R) = 1 :=
  (congrArg (rowHom m R) ofAdd_zero_fun).trans (map_one (rowHom m R))

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.rowProd_zero

theorem colProd_add (v w : Fin m → R) : colProd (v + w) = colProd v * colProd w :=
  (congrArg (colHom m R) (ofAdd_add_fun v w)).trans (map_mul (colHom m R) _ _)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.colProd_add

theorem rowProd_add (v w : Fin m → R) : rowProd (v + w) = rowProd v * rowProd w :=
  (congrArg (rowHom m R) (ofAdd_add_fun v w)).trans (map_mul (rowHom m R) _ _)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.rowProd_add

theorem colProd_single (i : Fin m) (a : R) : colProd (Pi.single i a) = colRoot m R i a :=
  (congrArg (colHom m R) (ofAdd_single i a)).trans
    (MonoidHom.noncommPiCoprod_mulSingle (colRootHom m R) (hcomm := colRootHom_commute m R) i
      (Multiplicative.ofAdd a))

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.colProd_single

theorem rowProd_single (i : Fin m) (a : R) : rowProd (Pi.single i a) = rowRoot m R i a :=
  (congrArg (rowHom m R) (ofAdd_single i a)).trans
    (MonoidHom.noncommPiCoprod_mulSingle (rowRootHom m R) (hcomm := rowRootHom_commute m R) i
      (Multiplicative.ofAdd a))

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.rowProd_single

end GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction
