import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.Vectors
import GroupApproximation.Meta.AxiomGuard

/-!
# The column and row action of `St_m(R)` on the boundary of `St_{m+1}(R)`

Lane `sk-rows-13`.  This module proves lane `sk-rows-14`'s interface
`PaddedCentrality.SteinbergColumnActionStatement m R` for every `m` and every ring `R`.  With
`paddedCentralityStatement_of_columnAction`, it closes `PaddedCentralityStatement m R`.

## Route

* `ColAction y`: `stab y · colProd v · (stab y)⁻¹ = colProd (M(y) v)` for all `v`.
  `RowAction y`: `stab y · rowProd w · (stab y)⁻¹ = rowProd (w M(y⁻¹))` for all `w`.
* Both predicates hold at `1` and are closed under products and inverses, because
  `M(y z) = M(y) M(z)`.
* Both hold at each generator `x_{pq}(c)`.  The basis vectors are handled in `Generators` and
  `Vectors`, and `conj_colProd_of_single` passes to all vectors.
* `PresentedGroup.generated_by` gives both predicates on all of `St_m(R)`.  At `v = e_i a`, the
  vector product is the `List.prod` of the interface (`colProd_eq_list`).
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality
open scoped Matrix

section Action

variable {m : ℕ} {R : Type*} [Ring R]

theorem colProd_eq_list (v : Fin m → R) :
    colProd v = ((List.finRange m).map fun k => colRoot m R k (v k)).prod :=
  (Finset.noncommProd_congr (f := fun k => colRoot m R k (v k))
      (g := fun k => colRoot m R k (v k)) (List.toFinset_finRange m).symm (fun _ _ => rfl)
      (fun k _ l _ _ => colRoot_commute m R k l (v k) (v l))).trans
    (Finset.noncommProd_toFinset (List.finRange m) (fun k => colRoot m R k (v k))
      (fun k _ l _ _ => colRoot_commute m R k l (v k) (v l)) (List.nodup_finRange m))

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.colProd_eq_list

theorem rowProd_eq_list (v : Fin m → R) :
    rowProd v = ((List.finRange m).map fun k => rowRoot m R k (v k)).prod :=
  (Finset.noncommProd_congr (f := fun k => rowRoot m R k (v k))
      (g := fun k => rowRoot m R k (v k)) (List.toFinset_finRange m).symm (fun _ _ => rfl)
      (fun k _ l _ _ => rowRoot_commute m R k l (v k) (v l))).trans
    (Finset.noncommProd_toFinset (List.finRange m) (fun k => rowRoot m R k (v k))
      (fun k _ l _ _ => rowRoot_commute m R k l (v k) (v l)) (List.nodup_finRange m))

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.rowProd_eq_list

/-- Conjugation by `stab y` acts on the last-column roots through `projection y`. -/
def ColAction (y : St m R) : Prop :=
  ∀ v : Fin m → R, stab m R y * colProd v * (stab m R y)⁻¹ = colProd (projectionMatrix m R y *ᵥ v)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.ColAction

/-- Conjugation by `stab y` acts on the last-row roots through `projection y⁻¹`. -/
def RowAction (y : St m R) : Prop :=
  ∀ w : Fin m → R, stab m R y * rowProd w * (stab m R y)⁻¹ = rowProd (w ᵥ* projectionMatrix m R y⁻¹)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.RowAction

theorem colAction_one : ColAction (1 : St m R) := by
  intro v
  simp only [map_one, inv_one, mul_one, one_mul, projectionMatrix_one, Matrix.one_mulVec]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.colAction_one

theorem rowAction_one : RowAction (1 : St m R) := by
  intro w
  simp only [map_one, inv_one, mul_one, one_mul, projectionMatrix_one, Matrix.vecMul_one]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.rowAction_one

theorem colAction_mul {a b : St m R} (ha : ColAction a) (hb : ColAction b) :
    ColAction (a * b) := by
  intro v
  rw [map_mul, mul_inv_rev, projectionMatrix_mul, ← Matrix.mulVec_mulVec,
    ← ha (projectionMatrix m R b *ᵥ v), ← hb v]
  simp only [mul_assoc]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.colAction_mul

theorem rowAction_mul {a b : St m R} (ha : RowAction a) (hb : RowAction b) :
    RowAction (a * b) := by
  intro w
  rw [map_mul, mul_inv_rev, mul_inv_rev, projectionMatrix_mul, ← Matrix.vecMul_vecMul,
    ← ha (w ᵥ* projectionMatrix m R b⁻¹), ← hb w]
  simp only [mul_assoc]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.rowAction_mul

theorem colAction_inv {a : St m R} (ha : ColAction a) : ColAction a⁻¹ := by
  intro v
  have h := ha (projectionMatrix m R a⁻¹ *ᵥ v)
  rw [Matrix.mulVec_mulVec, ← projectionMatrix_mul, mul_inv_cancel, projectionMatrix_one,
    Matrix.one_mulVec] at h
  rw [map_inv, inv_inv, ← h]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.colAction_inv

theorem rowAction_inv {a : St m R} (ha : RowAction a) : RowAction a⁻¹ := by
  intro w
  have h := ha (w ᵥ* projectionMatrix m R a)
  rw [Matrix.vecMul_vecMul, ← projectionMatrix_mul, mul_inv_cancel, projectionMatrix_one,
    Matrix.vecMul_one] at h
  rw [map_inv, inv_inv, inv_inv, ← h]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.rowAction_inv

theorem colAction_x (p q : Fin m) (hpq : p ≠ q) (c : R) :
    ColAction (SteinbergGroup.x p q hpq c) := by
  intro v
  rw [projectionMatrix_x]
  refine conj_colProd_of_single (stab m R (SteinbergGroup.x p q hpq c))
    (1 + Matrix.single p q c) (fun i a => ?_) v
  by_cases hiq : i = q
  · rw [hiq, conj_col_same p q hpq c a, col_vec_same p q hpq c a, colProd_add, colProd_single,
      colProd_single]
  · rw [conj_col_other p q hpq c hiq a, col_vec_other p q c hiq a, colProd_single]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.colAction_x

theorem rowAction_x (p q : Fin m) (hpq : p ≠ q) (c : R) :
    RowAction (SteinbergGroup.x p q hpq c) := by
  intro w
  rw [projectionMatrix_inv_x]
  refine conj_rowProd_of_single (stab m R (SteinbergGroup.x p q hpq c))
    (1 + Matrix.single p q (-c)) (fun i a => ?_) w
  by_cases hip : i = p
  · rw [hip, conj_row_same p q hpq c a, row_vec_same p q hpq (-c) a, rowProd_add,
      rowProd_single, rowProd_single]
  · rw [conj_row_other p q hpq c hip a, row_vec_other p q (-c) hip a, rowProd_single]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.rowAction_x

theorem colAction_all (y : St m R) : ColAction y := by
  have hy : y ∈ ({ carrier := {z | ColAction z}
      mul_mem' := fun {a b} ha hb => colAction_mul (a := a) (b := b) ha hb
      one_mem' := colAction_one (m := m) (R := R)
      inv_mem' := fun {a} ha => colAction_inv (a := a) ha } : Subgroup (St m R)) := by
    refine PresentedGroup.generated_by _ _ (fun j => ?_) y
    obtain ⟨p, q, hpq, c⟩ := j
    exact colAction_x p q hpq c
  exact hy

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.colAction_all

theorem rowAction_all (y : St m R) : RowAction y := by
  have hy : y ∈ ({ carrier := {z | RowAction z}
      mul_mem' := fun {a b} ha hb => rowAction_mul (a := a) (b := b) ha hb
      one_mem' := rowAction_one (m := m) (R := R)
      inv_mem' := fun {a} ha => rowAction_inv (a := a) ha } : Subgroup (St m R)) := by
    refine PresentedGroup.generated_by _ _ (fun j => ?_) y
    obtain ⟨p, q, hpq, c⟩ := j
    exact rowAction_x p q hpq c
  exact hy

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.rowAction_all

/-- **Endpoint of lane `sk-rows-13`.**  Lane `sk-rows-14`'s interface holds for every `m` and
every ring `R`. -/
theorem steinbergColumnActionStatement_holds (m : ℕ) (R : Type*) [Ring R] :
    SteinbergColumnActionStatement m R := by
  intro y i a
  constructor
  · rw [← colProd_single i a, colAction_all y (Pi.single i a), colProd_eq_list]
    simp only [mulVec_single_apply]
  · rw [← rowProd_single i a, rowAction_all y (Pi.single i a), rowProd_eq_list]
    simp only [vecMul_single_apply]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.steinbergColumnActionStatement_holds

/-- Padded centrality (Khanh, Lemma 5.6), unconditionally: `stab (K₂(m, R))` is central in
`St_{m+1}(R)`. -/
theorem paddedCentralityStatement_holds (m : ℕ) (R : Type*) [Ring R] :
    PaddedCentralityStatement m R :=
  paddedCentralityStatement_of_columnAction m R (steinbergColumnActionStatement_holds m R)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.paddedCentralityStatement_holds

end GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction
