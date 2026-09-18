import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Backward.PermAlg

/-!
# The carrier of the KMS model group

Input for the "if" direction of KMS Theorem `tmm`(b) (`l654`, `l789` of
Kharlampovich--Myasnikov--Sapir, arXiv:1204.6506, Sec. 4.1), used in
`thm:fixed-radical-membership` of `non_mf_group_notes.tex`.

The model group acts on pairs `(φ, t) ∈ X × 𝔽_2`.  An `x`-letter acts by a
translation `tau l : (φ, t) ↦ (φ, t + l φ)` for a functional `l : X → 𝔽_2`, and a
letter of `L_1 ∪ L_2` acts through a permutation `e` of `X` by `liftP e : (φ, t) ↦ (e φ, t)`.

This file proves the rules for these permutations:
* translations form an elementary abelian `2`-group (`tau_mul`, `tau_sq`, `tau_comm`);
* `tau` is injective (`tau_injective`);
* conjugating a translation by `liftP e` precomposes its functional with `e`
  (`khConj_tau_liftP`), and so do the commutator and the operation `khStar` of G8.
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

namespace Backward

variable {X : Type*}

theorem add_add_self_zmod (a b : ZMod 2) : a + b + b = a := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- The translation `(φ, t) ↦ (φ, t + l φ)` of an `x`-letter (KMS `l789`). -/
def tau (l : X → ZMod 2) : Equiv.Perm (X × ZMod 2) where
  toFun p := (p.1, p.2 + l p.1)
  invFun p := (p.1, p.2 + l p.1)
  left_inv p := Prod.ext rfl (add_add_self_zmod p.2 (l p.1))
  right_inv p := Prod.ext rfl (add_add_self_zmod p.2 (l p.1))

theorem tau_apply (l : X → ZMod 2) (p : X × ZMod 2) : tau l p = (p.1, p.2 + l p.1) := rfl

theorem tau_mul (l l' : X → ZMod 2) : tau l * tau l' = tau (l + l') := by
  refine Equiv.ext fun p ↦ Prod.ext rfl ?_
  show p.2 + l' p.1 + l p.1 = p.2 + (l p.1 + l' p.1)
  ring

theorem tau_zero : tau (0 : X → ZMod 2) = 1 := by
  refine Equiv.ext fun p ↦ Prod.ext rfl ?_
  show p.2 + 0 = p.2
  exact add_zero _

theorem add_self_fun (l : X → ZMod 2) : l + l = 0 :=
  funext fun x ↦ CharTwo.add_self_eq_zero (l x)

theorem tau_self (l : X → ZMod 2) : tau l * tau l = 1 := by
  rw [tau_mul, add_self_fun, tau_zero]

theorem tau_sq (l : X → ZMod 2) : tau l ^ 2 = 1 := by
  rw [pow_two, tau_self]

theorem tau_inv (l : X → ZMod 2) : (tau l)⁻¹ = tau l :=
  inv_eq_of_mul_eq_one_right (tau_self l)

theorem tau_comm (l l' : X → ZMod 2) : tau l * tau l' = tau l' * tau l := by
  rw [tau_mul, tau_mul, add_comm]

theorem khComm_tau_tau (l l' : X → ZMod 2) : khComm (tau l) (tau l') = 1 :=
  khComm_eq_one_of_mul_comm (tau_comm l l')

theorem tau_injective {l l' : X → ZMod 2} (h : tau l = tau l') : l = l' := by
  funext φ
  have h2 : (0 : ZMod 2) + l φ = 0 + l' φ :=
    congrArg (fun e : Equiv.Perm (X × ZMod 2) ↦ (e (φ, 0)).2) h
  rwa [zero_add, zero_add] at h2

/-- The permutation `(φ, t) ↦ (e φ, t)`. -/
def liftE (e : Equiv.Perm X) : Equiv.Perm (X × ZMod 2) where
  toFun p := (e p.1, p.2)
  invFun p := (e.symm p.1, p.2)
  left_inv p := Prod.ext (e.symm_apply_apply p.1) rfl
  right_inv p := Prod.ext (e.apply_symm_apply p.1) rfl

/-- A letter of `L_1 ∪ L_2` acts on the first coordinate only (KMS `l789`). -/
def liftP : Equiv.Perm X →* Equiv.Perm (X × ZMod 2) where
  toFun := liftE
  map_one' := Equiv.ext fun _ ↦ rfl
  map_mul' _ _ := Equiv.ext fun _ ↦ rfl

theorem liftP_apply (e : Equiv.Perm X) (p : X × ZMod 2) : liftP e p = (e p.1, p.2) := rfl

/-- Conjugating a translation by `liftP e` precomposes its functional with `e`. -/
theorem khConj_tau_liftP (l : X → ZMod 2) (e : Equiv.Perm X) :
    khConj (tau l) (liftP e) = tau (fun x ↦ l (e x)) := by
  refine Equiv.ext fun p ↦ Prod.ext ?_ rfl
  show e.symm (e p.1) = p.1
  exact e.symm_apply_apply p.1

/-- The commutator `[x, h]` adds the precomposed functional. -/
theorem khComm_tau_liftP (l : X → ZMod 2) (e : Equiv.Perm X) :
    khComm (tau l) (liftP e) = tau (l + fun x ↦ l (e x)) := by
  have h : khComm (tau l) (liftP e) = (tau l)⁻¹ * khConj (tau l) (liftP e) := by
    simp only [khComm, khConj, mul_assoc]
  rw [h, tau_inv, khConj_tau_liftP, tau_mul]

/-- The operation `khStar` of G8 on a translation (KMS `l789`). -/
theorem khStar_tau_liftP (l : X → ZMod 2) (a a' : Equiv.Perm X) :
    khStar (tau l) (liftP a) (liftP a') =
      tau (l + (fun x ↦ l (a x)) + (fun x ↦ l (a⁻¹ x)) + fun x ↦ l (a'⁻¹ x)) := by
  rw [khStar, ← map_inv liftP a, ← map_inv liftP a', khConj_tau_liftP, khConj_tau_liftP,
    khConj_tau_liftP, tau_inv, tau_inv, tau_mul, tau_mul, tau_mul]

end Backward

end KMS

end GroupApproximation.Full.Kharlampovich
