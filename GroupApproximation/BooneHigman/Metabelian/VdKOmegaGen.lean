import GroupApproximation.BooneHigman.Metabelian.VdKOmegaRowPar
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.StabAction
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn.VecProd
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# The amalgam route, part 2: generator values from two parabolic actions

Lane `bh-met-92j`.  Fix a group `G` and homomorphisms `α : P̃ →* G` and `β : P̃⁻ →* G` out of
the parabolic `P̃ = R^n ⋊ St_n(R)` (columns) and the opposite parabolic `P̃⁻ = R^n ⋊ St_n(R)`
(rows).  This file gives the would-be images of the roots of `St_{n+1}(R)`:

* `vdkOmega_cv α v`: the column part, image of `x(v) = ∏ x_{i,last}(v_i)`;
* `vdkOmega_rv β w`: the row part, image of `∏ x_{last,k}(w_k)`;
* `vdkOmega_sv α i j a`: the image of the `St_n` root `x_{ij}(a)` (`1` when `i = j`).

It also states the two gluing conditions:

* `vdkOmega_Agree α β`: `α` and `β` agree on `St_n(R)`;
* `vdkOmega_Mixed α β`: `⁅x_{i,last}(a), x_{last,k}(b)⁆ = x_{ik}(ab)` for `i ≠ k`.

Then it proves every Steinberg relator that follows from the semidirect-product structure alone,
unconditionally.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
  (projectionMatrix projectionMatrix_x projectionMatrix_x_inv)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.RowColumn
  (one_add_single_mulVec vecMul_one_add_single)
open scoped Matrix commutatorElement

variable {n : ℕ} {R : Type*} [CommRing R] {G : Type*} [Group G]

/-- The image of the column vector `v`, i.e. of `∏ x_{i,last}(v_i)`. -/
def vdkOmega_cv (α : vdkParPres_Tilde n R →* G) (v : Fin n → R) : G :=
  α (SemidirectProduct.inl (Multiplicative.ofAdd v))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_cv

/-- The image of the row vector `w`, i.e. of `∏ x_{last,k}(w_k)`. -/
def vdkOmega_rv (β : vdkOmega_TildeMinus n R →* G) (w : Fin n → R) : G :=
  β (SemidirectProduct.inl (Multiplicative.ofAdd w))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_rv

/-- The image of the `St_n` root `x_{ij}(a)`, and `1` on the diagonal. -/
def vdkOmega_sv (α : vdkParPres_Tilde n R →* G) (i j : Fin n) (a : R) : G :=
  if h : i = j then 1 else α (vdkParPres_inr (x i j h a))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_sv

/-- The two parabolic actions agree on `St_n(R)`. -/
def vdkOmega_Agree (α : vdkParPres_Tilde n R →* G) (β : vdkOmega_TildeMinus n R →* G) :
    Prop :=
  ∀ g : St n R, α (vdkParPres_inr g) = β (vdkOmega_inrMinus g)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_Agree

/-- The mixed relation `⁅x_{i,last}(a), x_{last,k}(b)⁆ = x_{ik}(ab)` for `i ≠ k`. -/
def vdkOmega_Mixed (α : vdkParPres_Tilde n R →* G) (β : vdkOmega_TildeMinus n R →* G) :
    Prop :=
  ∀ (i k : Fin n) (h : i ≠ k) (a b : R),
    ⁅vdkOmega_cv α (Pi.single i a), vdkOmega_rv β (Pi.single k b)⁆ =
      α (vdkParPres_inr (x i k h (a * b)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_Mixed

variable (α : vdkParPres_Tilde n R →* G) (β : vdkOmega_TildeMinus n R →* G)

theorem vdkOmega_sv_of_ne (i j : Fin n) (h : i ≠ j) (a : R) :
    vdkOmega_sv α i j a = α (vdkParPres_inr (x i j h a)) :=
  dif_neg h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_sv_of_ne

theorem vdkOmega_update_eq_single (i : Fin n) (t : R) :
    Function.update (0 : Fin n → R) i t = Pi.single i t :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_update_eq_single

theorem vdkOmega_cv_add (v w : Fin n → R) :
    vdkOmega_cv α (v + w) = vdkOmega_cv α v * vdkOmega_cv α w := by
  simp only [vdkOmega_cv, ofAdd_add, map_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_cv_add

theorem vdkOmega_cv_neg (v : Fin n → R) : vdkOmega_cv α (-v) = (vdkOmega_cv α v)⁻¹ := by
  simp only [vdkOmega_cv, ofAdd_neg, map_inv]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_cv_neg

theorem vdkOmega_rv_add (v w : Fin n → R) :
    vdkOmega_rv β (v + w) = vdkOmega_rv β v * vdkOmega_rv β w := by
  simp only [vdkOmega_rv, ofAdd_add, map_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_rv_add

theorem vdkOmega_rv_neg (v : Fin n → R) : vdkOmega_rv β (-v) = (vdkOmega_rv β v)⁻¹ := by
  simp only [vdkOmega_rv, ofAdd_neg, map_inv]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_rv_neg

/-- Conjugating a column vector by `g ∈ St_n` multiplies it by `M_g`. -/
theorem vdkOmega_conj_cv (g : St n R) (v : Fin n → R) :
    α (vdkParPres_inr g) * vdkOmega_cv α v * (α (vdkParPres_inr g))⁻¹ =
      vdkOmega_cv α (projectionMatrix g *ᵥ v) := by
  have h := congrArg α
    (SemidirectProduct.inl_aut (φ := vdkParPres_act) g (Multiplicative.ofAdd v))
  simp only [map_mul, map_inv] at h
  exact h.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_conj_cv

/-- Conjugating a row vector by `g ∈ St_n` multiplies it by `M_g⁻¹` on the right. -/
theorem vdkOmega_conj_rv (g : St n R) (w : Fin n → R) :
    β (vdkOmega_inrMinus g) * vdkOmega_rv β w * (β (vdkOmega_inrMinus g))⁻¹ =
      vdkOmega_rv β (w ᵥ* projectionMatrix g⁻¹) := by
  have h := congrArg β
    (SemidirectProduct.inl_aut (φ := vdkOmega_rowAct) g (Multiplicative.ofAdd w))
  simp only [map_mul, map_inv] at h
  exact h.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_conj_rv

/-- The row conjugation formula, with the `St_n` element taken through `α`. -/
theorem vdkOmega_conj_rv_alpha (hαβ : vdkOmega_Agree α β) (g : St n R) (w : Fin n → R) :
    α (vdkParPres_inr g) * vdkOmega_rv β w * (α (vdkParPres_inr g))⁻¹ =
      vdkOmega_rv β (w ᵥ* projectionMatrix g⁻¹) := by
  rw [hαβ g]
  exact vdkOmega_conj_rv β g w

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_conj_rv_alpha

/-! ### Commutators from conjugation formulas -/

theorem vdkOmega_comm_of_conj {S Y Y' : G} (h : S * Y * S⁻¹ = Y') : ⁅S, Y⁆ = Y' * Y⁻¹ := by
  rw [commutatorElement_def, h]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_comm_of_conj

theorem vdkOmega_comm_of_conj' {S Y Y' : G} (h : S * Y * S⁻¹ = Y') : ⁅Y, S⁆ = Y * Y'⁻¹ := by
  rw [commutatorElement_def, ← h]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_comm_of_conj'

theorem vdkOmega_comm_eq_one_of_conj {S Y : G} (h : S * Y * S⁻¹ = Y) : ⁅S, Y⁆ = 1 := by
  have hc : Commute S Y := mul_inv_eq_iff_eq_mul.mp h
  exact commutatorElement_eq_one_iff_commute.mpr hc

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_comm_eq_one_of_conj

theorem vdkOmega_comm_eq_one_of_conj' {S Y : G} (h : S * Y * S⁻¹ = Y) : ⁅Y, S⁆ = 1 := by
  have hc : Commute S Y := mul_inv_eq_iff_eq_mul.mp h
  exact commutatorElement_eq_one_iff_commute.mpr hc.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_comm_eq_one_of_conj'

/-! ### The relators that hold in each parabolic separately -/

theorem vdkOmega_inr_commutator (g h : St n R) :
    ⁅α (vdkParPres_inr g), α (vdkParPres_inr h)⁆ = α (vdkParPres_inr ⁅g, h⁆) := by
  simp only [map_commutatorElement]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_inr_commutator

theorem vdkOmega_cv_comm (v w : Fin n → R) : ⁅vdkOmega_cv α v, vdkOmega_cv α w⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_commute]
  show vdkOmega_cv α v * vdkOmega_cv α w = vdkOmega_cv α w * vdkOmega_cv α v
  rw [← vdkOmega_cv_add, ← vdkOmega_cv_add, add_comm]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_cv_comm

theorem vdkOmega_rv_comm (v w : Fin n → R) : ⁅vdkOmega_rv β v, vdkOmega_rv β w⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_commute]
  show vdkOmega_rv β v * vdkOmega_rv β w = vdkOmega_rv β w * vdkOmega_rv β v
  rw [← vdkOmega_rv_add, ← vdkOmega_rv_add, add_comm]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_rv_comm

/-- `x_{ij}(c)` fixes the column vector `b e_k` when `j ≠ k`. -/
theorem vdkOmega_conj_cv_triv (i j : Fin n) (h : i ≠ j) (c : R) (k : Fin n) (b : R)
    (hjk : j ≠ k) :
    α (vdkParPres_inr (x i j h c)) * vdkOmega_cv α (Pi.single k b) *
      (α (vdkParPres_inr (x i j h c)))⁻¹ = vdkOmega_cv α (Pi.single k b) := by
  rw [vdkOmega_conj_cv, projectionMatrix_x, one_add_single_mulVec, vdkOmega_update_eq_single,
    Pi.single_eq_of_ne hjk, mul_zero, Pi.single_zero, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_conj_cv_triv

/-- `x_{ij}(c)` fixes the row vector `b e_k` when `i ≠ k`. -/
theorem vdkOmega_conj_rv_triv (hαβ : vdkOmega_Agree α β) (i j : Fin n) (h : i ≠ j) (c : R)
    (k : Fin n) (b : R) (hik : i ≠ k) :
    α (vdkParPres_inr (x i j h c)) * vdkOmega_rv β (Pi.single k b) *
      (α (vdkParPres_inr (x i j h c)))⁻¹ = vdkOmega_rv β (Pi.single k b) := by
  rw [vdkOmega_conj_rv_alpha α β hαβ, projectionMatrix_x_inv, vecMul_one_add_single,
    vdkOmega_update_eq_single, Pi.single_eq_of_ne hik, zero_mul, Pi.single_zero, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_conj_rv_triv

/-- `⁅x_{ij}(c), x_{j,last}(b)⁆ = x_{i,last}(cb)`. -/
theorem vdkOmega_sv_cv_adj (i j : Fin n) (h : i ≠ j) (c b : R) :
    ⁅α (vdkParPres_inr (x i j h c)), vdkOmega_cv α (Pi.single j b)⁆ =
      vdkOmega_cv α (Pi.single i (c * b)) := by
  rw [vdkOmega_comm_of_conj (vdkOmega_conj_cv α (x i j h c) (Pi.single j b)),
    projectionMatrix_x, one_add_single_mulVec, vdkOmega_update_eq_single, Pi.single_eq_same,
    ← vdkOmega_cv_neg, ← vdkOmega_cv_add, add_right_comm, add_neg_cancel, zero_add]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_sv_cv_adj

/-- `⁅x_{last,j}(a), x_{jk}(b)⁆ = x_{last,k}(ab)`. -/
theorem vdkOmega_rv_sv_adj (hαβ : vdkOmega_Agree α β) (j k : Fin n) (h : j ≠ k) (a b : R) :
    ⁅vdkOmega_rv β (Pi.single j a), α (vdkParPres_inr (x j k h b))⁆ =
      vdkOmega_rv β (Pi.single k (a * b)) := by
  rw [vdkOmega_comm_of_conj' (vdkOmega_conj_rv_alpha α β hαβ (x j k h b) (Pi.single j a)),
    projectionMatrix_x_inv, vecMul_one_add_single, vdkOmega_update_eq_single,
    Pi.single_eq_same, ← vdkOmega_rv_neg, ← vdkOmega_rv_add, neg_add, ← add_assoc,
    add_neg_cancel, zero_add, ← Pi.single_neg, mul_neg, neg_neg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_rv_sv_adj

end GroupApproximation.BooneHigman.Metabelian.ElemFP
