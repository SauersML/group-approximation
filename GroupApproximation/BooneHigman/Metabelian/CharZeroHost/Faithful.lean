import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Defect
import Mathlib.RingTheory.Filtration
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Faithfulness of the char-zero host (lane bh-met-09)

Research claim: for a Noetherian char-zero domain `A` with `DigitData A p` (`1 < p`), the tree
representation `rho : A[t_1, …, t_k]^n ⋊ GL_n(A[t]) →* Aut(X^*)` is injective, so
`rho` is a faithful self-similar representation (`isSelfSimilarRep_rho`).

**Route.** If `rho x = 1`, every defect `evalN s (Zv x e j)` is divisible by all `p ^ N`
(`pow_dvd_evalN_Zv`), hence is `0` by Krull's intersection theorem
(`Ideal.iInf_pow_eq_bot_of_isDomain`, with `span {p} ≠ ⊤` since `p` reduces to `0` in the
nontrivial ring `ZMod p`).  A polynomial vanishing on `ℕ^k ⊆ A^k` is zero
(`MvPolynomial.funext_set`, `ℕ → A` injective).  With `e = 0` this gives `vec x = 0`; with
`e = Pi.single j 1` it gives the column `mat x *ᵥ e_j = e_j`, so `mat x = 1`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharZeroHost

open MvPolynomial
open scoped Matrix

variable {A : Type*} [CommRing A] {p n k : ℕ}

/-- `p` is not a unit of a ring with `DigitData A p`, `1 < p`. -/
theorem not_isUnit_natCast (D : DigitData A p) [Fact (1 < p)] : ¬IsUnit (p : A) := fun h => by
  have h2 := IsUnit.map D.red h
  rw [map_natCast, ZMod.natCast_self] at h2
  exact not_isUnit_zero h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.not_isUnit_natCast

/-- **Krull**: in a Noetherian domain an element divisible by all powers of a non-unit is `0`. -/
theorem eq_zero_of_pow_dvd [IsDomain A] [IsNoetherianRing A] {q : A} (hq : ¬IsUnit q) {r : A}
    (h : ∀ N : ℕ, q ^ N ∣ r) : r = 0 := by
  have hI : Ideal.span {q} ≠ ⊤ := fun h' => hq (Ideal.span_singleton_eq_top.1 h')
  have hr : r ∈ ⨅ N : ℕ, Ideal.span {q} ^ N := Ideal.mem_iInf.2 fun N => by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h N
  rw [Ideal.iInf_pow_eq_bot_of_isDomain (I := Ideal.span {q}) hI] at hr
  exact Ideal.mem_bot.1 hr

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.eq_zero_of_pow_dvd

/-- A polynomial over a char-zero domain vanishing at all natural points is `0`. -/
theorem eq_zero_of_evalN [IsDomain A] [CharZero A] {P : MvPolynomial (Fin k) A}
    (h : ∀ s : Fin k → ℕ, evalN s P = 0) : P = 0 := by
  refine MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → A))
    (fun _ => Set.infinite_range_of_injective Nat.cast_injective) fun y hy => ?_
  choose m hm using fun i => Set.mem_range.1 (Set.mem_univ_pi.1 hy i)
  have hy' : y = fun i => ((m i : ℕ) : A) := funext fun i => (hm i).symm
  rw [hy', map_zero]
  exact h m

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.eq_zero_of_evalN

/-- An affine map fixing every word is the identity. -/
theorem eq_one_of_fix [IsDomain A] [CharZero A] [IsNoetherianRing A] [NeZero p] [Fact (1 < p)]
    (D : DigitData A p) {x : Aff n (MvPolynomial (Fin k) A)} (hx : ∀ w, act D x w = w) :
    x = 1 := by
  have h0 : ∀ (s : Fin k → ℕ) (e : Fin n → ℕ) (j : Fin n), evalN s (Zv x e j) = 0 :=
    fun s e j => eq_zero_of_pow_dvd (not_isUnit_natCast D) fun N => pow_dvd_evalN_Zv D N x hx s e j
  have hv : vec x = 0 := funext fun j => eq_zero_of_evalN fun s => by
    have h := h0 s 0 j
    rw [Zv, natVec_zero, Matrix.mulVec_zero, zero_add, sub_zero] at h
    exact h
  refine eq_one_of_vec_mat hv (Matrix.ext fun i j0 => ?_)
  have hz : Zv x (Pi.single j0 1) i = 0 := eq_zero_of_evalN fun s => h0 s _ i
  rw [Zv, hv, add_zero, natVec_single, Pi.sub_apply, sub_eq_zero] at hz
  have hcol : (mat x *ᵥ Pi.single j0 1) i = mat x i j0 :=
    congrFun (Matrix.mulVec_single_one (mat x) j0) i
  have hone : (Pi.single j0 1 : Fin n → MvPolynomial (Fin k) A) i =
      (1 : Matrix (Fin n) (Fin n) (MvPolynomial (Fin k) A)) i j0 := by
    have h1 := congrFun
      (Matrix.mulVec_single_one (1 : Matrix (Fin n) (Fin n) (MvPolynomial (Fin k) A)) j0) i
    rw [Matrix.one_mulVec] at h1
    exact h1
  rw [hcol, hone] at hz
  exact hz

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.eq_one_of_fix

/-- **Faithfulness**: the tree representation is injective. -/
theorem rho_injective [IsDomain A] [CharZero A] [IsNoetherianRing A] [NeZero p] [Fact (1 < p)]
    (D : DigitData A p) : Function.Injective (rho (n := n) (k := k) D) :=
  (injective_iff_map_eq_one (rho (n := n) (k := k) D)).2 fun x hx =>
    eq_one_of_fix D fun w =>
      (rho_smul D x w).symm.trans ((congrArg (· • w) hx).trans (one_smul _ w))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.rho_injective

/-- **Endpoint**: `A[t_1, …, t_k]^n ⋊ GL_n(A[t])` has a faithful self-similar action on the tree
over `F_p^n × F_p^k`. -/
theorem isSelfSimilarRep_rho [IsDomain A] [CharZero A] [IsNoetherianRing A] [NeZero p]
    [Fact (1 < p)] (D : DigitData A p) :
    Trees.IsSelfSimilarRep (rho (n := n) (k := k) D) :=
  ⟨rho_injective D, isSelfSimilar_range_rho D⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.isSelfSimilarRep_rho

end CharZeroHost
end Metabelian
end BooneHigman
end GroupApproximation
