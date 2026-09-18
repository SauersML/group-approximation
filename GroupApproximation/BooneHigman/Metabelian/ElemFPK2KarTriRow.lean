import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.ConjRow
import GroupApproximation.Meta.AxiomGuard

/-!
# Last-row commutators `⁅x_{i,N}(β), padRow w⁆` with `w_i = 0`

Lane `bh-met-93k`, row module.  Over a ring `R`, write `N = Fin.last n`, and
`off i w = w - e_i(w_i)` for the vector `w` with its `i`-th entry removed.

* `k2KarTri_comm_mul_of_commute`: `⁅a, b c⁆ = ⁅a, b⁆ ⁅a, c⁆` when `⁅a, c⁆` commutes with `b`.
* `k2KarTri_row_commute`: `⁅x_{i,N}(β), padRow (off i w)⁆` commutes with every
  `padRow (off i w')`.  It is a product of roots `x_{i,q}` with `q ≠ i`, and these commute with
  every `x_{N,p}` with `p ≠ i`.
* `k2KarTri_row_add`: `⁅x_{i,N}(β), padRow (u + w)⁆ = ⁅x_{i,N}(β), padRow u⁆ ⁅x_{i,N}(β), padRow w⁆`
  when `u_i = w_i = 0`.
* `k2KarTri_row_smul`: `⁅x_{i,N}(β), padRow w⁆ = ⁅x_{i,N}(1), padRow (β • w)⁆` when `w_i = 0`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
open scoped commutatorElement

section KarTriGroup

/-- `⁅a, b c⁆ = ⁅a, b⁆ ⁅a, c⁆` when `⁅a, c⁆` commutes with `b`. -/
theorem k2KarTri_comm_mul_of_commute {G : Type*} [Group G] (a b c : G)
    (h : Commute ⁅a, c⁆ b) : ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have e : ⁅a, b * c⁆ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, ← h.eq, mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_comm_mul_of_commute

/-- `⁅b c, a⁆ = ⁅c, a⁆ ⁅b, a⁆` when `⁅c, a⁆` commutes with `b`. -/
theorem k2KarTri_mul_comm_of_commute {G : Type*} [Group G] (a b c : G)
    (h : Commute ⁅c, a⁆ b) : ⁅b * c, a⁆ = ⁅c, a⁆ * ⁅b, a⁆ := by
  have e : ⁅b * c, a⁆ = (b * ⁅c, a⁆ * b⁻¹) * ⁅b, a⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, ← h.eq, mul_inv_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_mul_comm_of_commute

end KarTriGroup

section KarTriOff

variable {R : Type*} [Ring R] {n : ℕ}

/-- The vector `w` with its `i`-th entry removed. -/
def k2KarTri_off (i : Fin n) (w : Fin n → R) : Fin n → R :=
  w - Pi.single i (w i)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_off

theorem k2KarTri_off_apply_self (i : Fin n) (w : Fin n → R) : k2KarTri_off i w i = 0 := by
  rw [k2KarTri_off, Pi.sub_apply, Pi.single_eq_same, sub_self]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_off_apply_self

theorem k2KarTri_off_of_apply {i : Fin n} {w : Fin n → R} (hw : w i = 0) :
    k2KarTri_off i w = w := by
  rw [k2KarTri_off, hw, Pi.single_zero, sub_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_off_of_apply

theorem k2KarTri_off_zero (i : Fin n) : k2KarTri_off i (0 : Fin n → R) = 0 := by
  rw [k2KarTri_off, Pi.zero_apply, Pi.single_zero, sub_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_off_zero

theorem k2KarTri_off_add (i : Fin n) (u w : Fin n → R) :
    k2KarTri_off i (u + w) = k2KarTri_off i u + k2KarTri_off i w := by
  funext q
  simp only [k2KarTri_off, Pi.add_apply, Pi.sub_apply, Pi.single_add]
  abel

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_off_add

theorem k2KarTri_off_single_self (i : Fin n) (a : R) :
    k2KarTri_off i (Pi.single i a) = 0 := by
  rw [k2KarTri_off, Pi.single_eq_same, sub_self]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_off_single_self

theorem k2KarTri_off_single_of_ne {i p : Fin n} (hp : p ≠ i) (a : R) :
    k2KarTri_off i (Pi.single p a) = Pi.single p a := by
  rw [k2KarTri_off, Pi.single_eq_of_ne' hp a, Pi.single_zero, sub_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_off_single_of_ne

theorem k2KarTri_smul_off (i : Fin n) (β : R) (w : Fin n → R) :
    β • k2KarTri_off i w = k2KarTri_off i (β • w) := by
  funext q
  by_cases hq : q = i
  · subst hq
    simp only [k2KarTri_off, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, sub_self,
      smul_zero]
  · simp only [k2KarTri_off, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_of_ne hq, sub_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_smul_off

theorem k2KarTri_smul_single (β a : R) (p : Fin n) :
    β • (Pi.single p a : Fin n → R) = Pi.single p (β * a) := by
  funext q
  by_cases hq : q = p
  · subst hq
    rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul]
  · rw [Pi.smul_apply, Pi.single_eq_of_ne hq, Pi.single_eq_of_ne hq, smul_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_smul_single

theorem k2KarTri_smul_apply_eq_zero {i : Fin n} {w : Fin n → R} (β : R) (hw : w i = 0) :
    (β • w) i = 0 := by
  rw [Pi.smul_apply, hw, smul_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_smul_apply_eq_zero

end KarTriOff

section KarTriRow

variable {R : Type*} [Ring R] {n : ℕ}

/-- A root `x_{i,q}` commutes with `padRow (off i w)`. -/
theorem k2KarTri_x_commute_padRow_off (i q : Fin n) (hcs : i.castSucc ≠ q.castSucc) (a : R)
    (w : Fin n → R) :
    Commute (x i.castSucc q.castSucc hcs a) (padRow (k2KarTri_off i w)) := by
  induction w using Pi.single_induction with
  | zero =>
    rw [k2KarTri_off_zero, padRow_zero]
    exact Commute.one_right _
  | add f g hf hg =>
    rw [k2KarTri_off_add, padRow_add]
    exact hf.mul_right hg
  | single p b =>
    by_cases hp : p = i
    · rw [hp, k2KarTri_off_single_self, padRow_zero]
      exact Commute.one_right _
    · rw [k2KarTri_off_single_of_ne hp, padRow_single]
      exact x_commute_of_ne i.castSucc q.castSucc (Fin.last n) p.castSucc hcs
        (Fin.castSucc_lt_last p).ne' (Fin.castSucc_lt_last q).ne
        (fun e ↦ hp (Fin.castSucc_inj.mp e)) a b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_x_commute_padRow_off

/-- `⁅x_{i,N}(β), padRow (off i w)⁆` commutes with every `padRow (off i w')`. -/
theorem k2KarTri_row_commute (i : Fin n) (β : R) (w : Fin n → R) :
    ∀ w' : Fin n → R, Commute ⁅x i.castSucc (Fin.last n) (Fin.castSucc_lt_last i).ne β,
      padRow (k2KarTri_off i w)⁆ (padRow (k2KarTri_off i w')) := by
  induction w using Pi.single_induction with
  | zero =>
    intro w'
    rw [k2KarTri_off_zero, padRow_zero, commutatorElement_one_right]
    exact Commute.one_left _
  | add f g hf hg =>
    intro w'
    rw [k2KarTri_off_add, padRow_add, k2KarTri_comm_mul_of_commute _ _ _ (hg f)]
    exact (hf w').mul_left (hg w')
  | single p a =>
    intro w'
    by_cases hp : p = i
    · rw [hp, k2KarTri_off_single_self, padRow_zero, commutatorElement_one_right]
      exact Commute.one_left _
    · rw [k2KarTri_off_single_of_ne hp, padRow_single,
        x_commutator i.castSucc (Fin.last n) p.castSucc (Fin.castSucc_lt_last i).ne
          (Fin.castSucc_lt_last p).ne' (fun e ↦ hp (Fin.castSucc_inj.mp e).symm) β a]
      exact k2KarTri_x_commute_padRow_off i p _ (β * a) w'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_row_commute

/-- Additivity of `w ↦ ⁅x_{i,N}(β), padRow w⁆` on vectors with vanishing `i`-th entry. -/
theorem k2KarTri_row_add (i : Fin n) (β : R) {u w : Fin n → R} (hu : u i = 0) (hw : w i = 0) :
    ⁅x i.castSucc (Fin.last n) (Fin.castSucc_lt_last i).ne β, padRow (u + w)⁆ =
      ⁅x i.castSucc (Fin.last n) (Fin.castSucc_lt_last i).ne β, padRow u⁆ *
        ⁅x i.castSucc (Fin.last n) (Fin.castSucc_lt_last i).ne β, padRow w⁆ := by
  have hc := k2KarTri_row_commute i β w u
  rw [k2KarTri_off_of_apply hw, k2KarTri_off_of_apply hu] at hc
  rw [padRow_add, k2KarTri_comm_mul_of_commute _ _ _ hc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_row_add

theorem k2KarTri_row_smul_off (i : Fin n) (β : R) (w : Fin n → R) :
    ⁅x i.castSucc (Fin.last n) (Fin.castSucc_lt_last i).ne β, padRow (k2KarTri_off i w)⁆ =
      ⁅x i.castSucc (Fin.last n) (Fin.castSucc_lt_last i).ne 1,
        padRow (β • k2KarTri_off i w)⁆ := by
  induction w using Pi.single_induction with
  | zero =>
    rw [k2KarTri_off_zero, smul_zero, padRow_zero, commutatorElement_one_right,
      commutatorElement_one_right]
  | add f g hf hg =>
    have hc := k2KarTri_row_commute i (1 : R) (β • g) (β • f)
    rw [← k2KarTri_smul_off, ← k2KarTri_smul_off] at hc
    rw [k2KarTri_off_add, smul_add, padRow_add, padRow_add,
      k2KarTri_comm_mul_of_commute _ _ _ (k2KarTri_row_commute i β g f),
      k2KarTri_comm_mul_of_commute _ _ _ hc, hf, hg]
  | single p a =>
    by_cases hp : p = i
    · rw [hp, k2KarTri_off_single_self, smul_zero, padRow_zero, commutatorElement_one_right,
        commutatorElement_one_right]
    · rw [k2KarTri_off_single_of_ne hp, k2KarTri_smul_single, padRow_single, padRow_single,
        x_commutator i.castSucc (Fin.last n) p.castSucc (Fin.castSucc_lt_last i).ne
          (Fin.castSucc_lt_last p).ne' (fun e ↦ hp (Fin.castSucc_inj.mp e).symm) β a,
        x_commutator i.castSucc (Fin.last n) p.castSucc (Fin.castSucc_lt_last i).ne
          (Fin.castSucc_lt_last p).ne' (fun e ↦ hp (Fin.castSucc_inj.mp e).symm) 1 (β * a),
        one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_row_smul_off

/-- `⁅x_{i,N}(β), padRow w⁆ = ⁅x_{i,N}(1), padRow (β • w)⁆` when `w_i = 0`. -/
theorem k2KarTri_row_smul (i : Fin n) (β : R) {w : Fin n → R} (hw : w i = 0) :
    ⁅x i.castSucc (Fin.last n) (Fin.castSucc_lt_last i).ne β, padRow w⁆ =
      ⁅x i.castSucc (Fin.last n) (Fin.castSucc_lt_last i).ne 1, padRow (β • w)⁆ := by
  have e := k2KarTri_row_smul_off i β w
  rwa [k2KarTri_off_of_apply hw] at e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarTri_row_smul

end KarTriRow

end GroupApproximation.BooneHigman.Metabelian.ElemFP
