import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.State
import GroupApproximation.BooneHigman.Trees.TreeAut

/-!
# The self-similar action of the char-zero affine group (lane bh-met-09)

Research claim: `R^n ⋊ GL_n(R)`, `R = A[t_1, …, t_k]`, acts on `X^*`, `X = F_p^n × F_p^k`, by
`(x) · (ℓ w) = letter x ℓ · (stateG x ℓ) · w`, and this action is self-similar.

**Route.** `act` is defined by recursion on words; `act_one` (`letter 1 ℓ = ℓ`,
`stateG 1 ℓ = 1`) and `act_mul` (the cocycle rules `outDigit_mul`, `stateG_mul`) make it an
action; lengths and prefixes are preserved, so `rho : Aff →* TreeAut X`.  The state of `rho x`
at the letter `ℓ` is `rho (stateG x ℓ)` (`state_rho`), so the range is self-similar.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharZeroHost

open MvPolynomial
open scoped Matrix

variable {A : Type*} [CommRing A] {p n k : ℕ} (D : DigitData A p)

/-- The action on words. -/
noncomputable def act (x : Aff n (MvPolynomial (Fin k) A)) :
    List (Letter p n k) → List (Letter p n k)
  | [] => []
  | ℓ :: w => letter D x ℓ :: act (stateG D x ℓ) w

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.act

theorem act_nil (x : Aff n (MvPolynomial (Fin k) A)) : act D x [] = [] := by
  rw [act]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.act_nil

theorem act_cons (x : Aff n (MvPolynomial (Fin k) A)) (ℓ : Letter p n k) (w : List (Letter p n k)) :
    act D x (ℓ :: w) = letter D x ℓ :: act D (stateG D x ℓ) w := by
  rw [act]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.act_cons

theorem act_length (x : Aff n (MvPolynomial (Fin k) A)) (w : List (Letter p n k)) :
    (act D x w).length = w.length := by
  induction w generalizing x with
  | nil => rw [act_nil]
  | cons ℓ w ih => rw [act_cons, List.length_cons, List.length_cons, ih]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.act_length

theorem act_prefix (x : Aff n (MvPolynomial (Fin k) A)) (w v : List (Letter p n k)) :
    act D x w <+: act D x (w ++ v) := by
  induction w generalizing x with
  | nil => rw [act_nil]; exact List.nil_prefix
  | cons ℓ w ih =>
    rw [List.cons_append, act_cons, act_cons]
    exact List.cons_prefix_cons.2 ⟨rfl, ih _⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.act_prefix

variable [NeZero p]

theorem letter_one (ℓ : Letter p n k) : letter D (1 : Aff n (MvPolynomial (Fin k) A)) ℓ = ℓ := by
  refine Prod.ext (funext fun j => ?_) rfl
  show dig D ℓ.2 (((1 : Matrix (Fin n) (Fin n) (MvPolynomial (Fin k) A)) *ᵥ castVec ℓ.1 + 0) j) =
    ℓ.1 j
  rw [Matrix.one_mulVec, add_zero, dig_castVec]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.letter_one

theorem letter_mul (x y : Aff n (MvPolynomial (Fin k) A)) (ℓ : Letter p n k) :
    letter D (x * y) ℓ = letter D x (letter D y ℓ) :=
  Prod.ext (outDigit_mul D x y ℓ) rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.letter_mul

variable [IsDomain A] [CharZero A]

theorem stateG_one (ℓ : Letter p n k) : stateG D (1 : Aff n (MvPolynomial (Fin k) A)) ℓ = 1 := by
  have hz : z D (1 : Aff n (MvPolynomial (Fin k) A)) ℓ = 0 := by
    rw [z, letter_one_fst D ℓ, mat_one, vec_one, Matrix.one_mulVec, add_zero, sub_self]
  have hp : (p : MvPolynomial (Fin k) A) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
  refine eq_one_of_vec_mat ?_ ?_
  · funext j
    have h := sigmaZ_z D (1 : Aff n (MvPolynomial (Fin k) A)) ℓ j
    rw [hz, Pi.zero_apply, map_zero] at h
    exact (mul_eq_zero.1 h.symm).resolve_left hp
  · show ((Matrix.GeneralLinearGroup.map (sigmaZ p ℓ.2) 1 :
      GL (Fin n) (MvPolynomial (Fin k) A)) : Matrix (Fin n) (Fin n) (MvPolynomial (Fin k) A)) = 1
    rw [map_one, Units.val_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.stateG_one

theorem act_one (w : List (Letter p n k)) :
    act D (1 : Aff n (MvPolynomial (Fin k) A)) w = w := by
  induction w with
  | nil => rw [act_nil]
  | cons ℓ w ih => rw [act_cons, letter_one, stateG_one, ih]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.act_one

theorem act_mul (x y : Aff n (MvPolynomial (Fin k) A)) (w : List (Letter p n k)) :
    act D (x * y) w = act D x (act D y w) := by
  induction w generalizing x y with
  | nil => rw [act_nil, act_nil, act_nil]
  | cons ℓ w ih => rw [act_cons, act_cons, act_cons, letter_mul, stateG_mul, ih]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.act_mul

/-- The action of an affine map as a permutation of words. -/
noncomputable def actPerm (x : Aff n (MvPolynomial (Fin k) A)) :
    Equiv.Perm (List (Letter p n k)) where
  toFun := act D x
  invFun := act D x⁻¹
  left_inv w := by rw [← act_mul, inv_mul_cancel, act_one]
  right_inv w := by rw [← act_mul, mul_inv_cancel, act_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.actPerm

/-- The tree representation `Aff n R →* Aut(X^*)`. -/
noncomputable def rho : Aff n (MvPolynomial (Fin k) A) →* Trees.TreeAut (Letter p n k) where
  toFun x := ⟨actPerm D x,
    show Trees.IsTreeMap (actPerm D x) from And.intro (act_length D x) (act_prefix D x)⟩
  map_one' := Trees.TreeAut.ext fun w => act_one D w
  map_mul' x y := Trees.TreeAut.ext fun w => act_mul D x y w

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.rho

theorem rho_smul (x : Aff n (MvPolynomial (Fin k) A)) (w : List (Letter p n k)) :
    rho D x • w = act D x w := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.rho_smul

/-- The state of `rho x` at a letter is `rho` of the state. -/
theorem state_rho (x : Aff n (MvPolynomial (Fin k) A)) (ℓ : Letter p n k) :
    Trees.TreeAut.state (rho D x) [ℓ] = rho D (stateG D x ℓ) := by
  refine Trees.TreeAut.ext fun v => Trees.TreeAut.state_smul_eq_of_smul_append _ ?_
  rw [rho_smul, rho_smul, rho_smul, List.cons_append, List.nil_append, act_cons, act_cons,
    act_nil, List.cons_append, List.nil_append]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.state_rho

theorem isSelfSimilar_range_rho : Trees.IsSelfSimilar (rho D (n := n) (k := k)).range :=
  (Trees.isSelfSimilar_range_iff (rho D)).2 fun x ℓ => ⟨stateG D x ℓ, state_rho D x ℓ⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.isSelfSimilar_range_rho

end CharZeroHost
end Metabelian
end BooneHigman
end GroupApproximation
