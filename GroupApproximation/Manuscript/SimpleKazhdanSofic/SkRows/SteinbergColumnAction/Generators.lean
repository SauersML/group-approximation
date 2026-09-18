import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.RootProducts
import GroupApproximation.Meta.AxiomGuard

/-!
# Conjugating boundary roots by a stabilized Steinberg generator

Lane `sk-rows-13`.  No single tex sentence is formalized here.

For a generator `y = x_{pq}(c)` of `St_m(R)`, write `p', q'` for the indices in `St_{m+1}(R)`
and `∞` for the last index.

* `conj_col_same`: `x_{p'q'}(c) · x_{q'∞}(a) · x_{p'q'}(c)⁻¹ = x_{p'∞}(c a) · x_{q'∞}(a)`, from the
  commutator relation `⁅x_{p'q'}(c), x_{q'∞}(a)⁆ = x_{p'∞}(c a)`.
* `conj_col_other`: `x_{p'q'}(c)` commutes with `x_{i'∞}(a)` for `i ≠ q`.
* `conj_row_same`: `x_{p'q'}(c) · x_{∞p'}(a) · x_{p'q'}(c)⁻¹ = x_{∞p'}(a) · x_{∞q'}(a (-c))`, from
  `⁅x_{∞p'}(-a), x_{p'q'}(c)⁆ = x_{∞q'}((-a) c)`.
* `conj_row_other`: `x_{p'q'}(c)` commutes with `x_{∞i'}(a)` for `i ≠ p`.

The projection matrix of `x_{pq}(c)` is `1 + c e_{pq}`, and that of its inverse is `1 + (-c) e_{pq}`.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality
open scoped Matrix commutatorElement

variable {m : ℕ} {R : Type*} [Ring R]

theorem mulVec_single_apply (M : Matrix (Fin m) (Fin m) R) (i : Fin m) (a : R) (k : Fin m) :
    (M *ᵥ Pi.single i a) k = M k i * a :=
  dotProduct_single (fun j => M k j) a i

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.mulVec_single_apply

theorem vecMul_single_apply (M : Matrix (Fin m) (Fin m) R) (i : Fin m) (a : R) (k : Fin m) :
    (Pi.single i a ᵥ* M) k = a * M i k :=
  single_dotProduct (fun j => M j k) a i

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.vecMul_single_apply

theorem projectionMatrix_mul (y z : St m R) :
    projectionMatrix m R (y * z) = projectionMatrix m R y * projectionMatrix m R z :=
  congrArg (fun g : elementaryGroup (Fin m) R =>
      ((g : (Matrix (Fin m) (Fin m) R)ˣ) : Matrix (Fin m) (Fin m) R))
    (map_mul (SteinbergGroup.projection (I := Fin m) (R := R)) y z)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.projectionMatrix_mul

theorem projectionMatrix_one : projectionMatrix m R 1 = 1 :=
  congrArg (fun g : elementaryGroup (Fin m) R =>
      ((g : (Matrix (Fin m) (Fin m) R)ˣ) : Matrix (Fin m) (Fin m) R))
    (map_one (SteinbergGroup.projection (I := Fin m) (R := R)))

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.projectionMatrix_one

theorem projectionMatrix_x (p q : Fin m) (hpq : p ≠ q) (c : R) :
    projectionMatrix m R (SteinbergGroup.x p q hpq c) = 1 + Matrix.single p q c :=
  congrArg (fun g : elementaryGroup (Fin m) R =>
      ((g : (Matrix (Fin m) (Fin m) R)ˣ) : Matrix (Fin m) (Fin m) R))
    (SteinbergGroup.projection_x p q hpq c)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.projectionMatrix_x

theorem projectionMatrix_inv_x (p q : Fin m) (hpq : p ≠ q) (c : R) :
    projectionMatrix m R (SteinbergGroup.x p q hpq c)⁻¹ = 1 + Matrix.single p q (-c) := by
  rw [← SteinbergGroup.x_neg]
  exact projectionMatrix_x p q hpq (-c)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.projectionMatrix_inv_x

theorem castSucc_ne_castSucc {p q : Fin m} (hpq : p ≠ q) : p.castSucc ≠ q.castSucc :=
  fun h => hpq (Fin.castSucc_inj.mp h)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.castSucc_ne_castSucc

theorem conj_col_same (p q : Fin m) (hpq : p ≠ q) (c a : R) :
    stab m R (SteinbergGroup.x p q hpq c) * colRoot m R q a *
        (stab m R (SteinbergGroup.x p q hpq c))⁻¹ =
      colRoot m R p (c * a) * colRoot m R q a := by
  have hc := SteinbergGroup.x_commutator (R := R) p.castSucc q.castSucc (Fin.last m)
    (castSucc_ne_castSucc hpq) (Fin.castSucc_ne_last q) (Fin.castSucc_ne_last p) c a
  rw [commutatorElement_def] at hc
  rw [stab_x]
  simp only [colRoot]
  rw [← hc]
  exact (inv_mul_cancel_right _ _).symm

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.conj_col_same

theorem conj_col_other (p q : Fin m) (hpq : p ≠ q) (c : R) {i : Fin m} (hiq : i ≠ q) (a : R) :
    stab m R (SteinbergGroup.x p q hpq c) * colRoot m R i a *
        (stab m R (SteinbergGroup.x p q hpq c))⁻¹ = colRoot m R i a := by
  rw [stab_x]
  exact (SteinbergGroup.x_commute_of_ne p.castSucc q.castSucc i.castSucc (Fin.last m)
    (castSucc_ne_castSucc hpq) (Fin.castSucc_ne_last i) (castSucc_ne_castSucc hiq.symm)
    (Fin.castSucc_ne_last p).symm c a).mul_inv_cancel

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.conj_col_other

theorem conj_row_same (p q : Fin m) (hpq : p ≠ q) (c a : R) :
    stab m R (SteinbergGroup.x p q hpq c) * rowRoot m R p a *
        (stab m R (SteinbergGroup.x p q hpq c))⁻¹ =
      rowRoot m R p a * rowRoot m R q (a * -c) := by
  have hc := SteinbergGroup.x_commutator (R := R) (Fin.last m) p.castSucc q.castSucc
    (Fin.castSucc_ne_last p).symm (castSucc_ne_castSucc hpq) (Fin.castSucc_ne_last q).symm (-a) c
  rw [SteinbergGroup.x_neg, commutatorElement_def, inv_inv, neg_mul_comm] at hc
  rw [stab_x]
  simp only [rowRoot]
  rw [← hc]
  simp only [mul_assoc, mul_inv_cancel_left]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.conj_row_same

theorem conj_row_other (p q : Fin m) (hpq : p ≠ q) (c : R) {i : Fin m} (hip : i ≠ p) (a : R) :
    stab m R (SteinbergGroup.x p q hpq c) * rowRoot m R i a *
        (stab m R (SteinbergGroup.x p q hpq c))⁻¹ = rowRoot m R i a := by
  rw [stab_x]
  exact (SteinbergGroup.x_commute_of_ne p.castSucc q.castSucc (Fin.last m) i.castSucc
    (castSucc_ne_castSucc hpq) (Fin.castSucc_ne_last i).symm (Fin.castSucc_ne_last q)
    (castSucc_ne_castSucc hip) c a).mul_inv_cancel

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction.conj_row_other

end GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergColumnAction
