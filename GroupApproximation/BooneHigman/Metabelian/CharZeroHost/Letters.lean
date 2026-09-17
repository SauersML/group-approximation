import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# Substitutions and digits of the char-zero host (lane bh-met-09)

Research claim: for `R = A[t_1, …, t_k]` and a first-level parameter `a ∈ F_p^k`, the substitution
`σ_a : t_j ↦ a_j + p t_j` satisfies `σ_a(P) ≡ P(a) (mod p)`, so the state
`(σ_a g e + σ_a b - c) / p` is a polynomial vector.

Here the coefficient ring `A` is abstract and comes with `DigitData A p`: a ring hom
`red : A →+* ZMod p` whose kernel is `p A`.  (For `A = Z[1/m]` with `p ∤ m` this is reduction
mod `p`.)  Parameters are natural numbers (the `val` of the `F_p` digits).

**Route.** `exists_sigma_eq`: `σ_a(P) = C (P(a)) + p q` by `MvPolynomial.induction_on`
(constants: `q = 0`; sums: add; `P * X_j`: `q' = q (a_j + p X_j) + C (P(a)) X_j`).
`divP p r` picks the quotient of `r` by `p` when it exists.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace CharZeroHost

open MvPolynomial

/-- Reduction data: a ring hom onto `ZMod p` whose kernel is `p A`. -/
structure DigitData (A : Type*) [CommRing A] (p : ℕ) where
  /-- The reduction map. -/
  red : A →+* ZMod p
  /-- Its kernel is `p A`. -/
  exists_eq_mul : ∀ x : A, red x = 0 → ∃ y : A, x = (p : A) * y

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.DigitData

variable {A : Type*} [CommRing A] {k : ℕ}

/-- Evaluation at a natural-number point. -/
def evalN (s : Fin k → ℕ) : MvPolynomial (Fin k) A →+* A :=
  MvPolynomial.eval fun i => ((s i : ℕ) : A)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.evalN

theorem evalN_C (s : Fin k → ℕ) (r : A) : evalN s (C r) = r :=
  MvPolynomial.eval_C r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.evalN_C

theorem evalN_X (s : Fin k → ℕ) (i : Fin k) :
    evalN s (X i : MvPolynomial (Fin k) A) = (s i : A) :=
  MvPolynomial.eval_X i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.evalN_X

variable (p : ℕ)

/-- The substitution `σ_a : t_j ↦ a_j + p t_j`. -/
def sigma (a : Fin k → ℕ) : MvPolynomial (Fin k) A →+* MvPolynomial (Fin k) A :=
  eval₂Hom C fun i => ((a i : ℕ) : MvPolynomial (Fin k) A) + (p : MvPolynomial (Fin k) A) * X i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.sigma

theorem sigma_C (a : Fin k → ℕ) (r : A) : sigma p a (C r) = C r :=
  eval₂Hom_C _ _ r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.sigma_C

theorem sigma_X (a : Fin k → ℕ) (i : Fin k) :
    sigma p a (X i : MvPolynomial (Fin k) A) =
      ((a i : ℕ) : MvPolynomial (Fin k) A) + (p : MvPolynomial (Fin k) A) * X i :=
  eval₂Hom_X' _ _ i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.sigma_X

/-- **Divisibility**: `σ_a(P) = C (P(a)) + p q` for some polynomial `q`. -/
theorem exists_sigma_eq (a : Fin k → ℕ) (P : MvPolynomial (Fin k) A) :
    ∃ q : MvPolynomial (Fin k) A,
      sigma p a P = C (evalN a P) + (p : MvPolynomial (Fin k) A) * q := by
  induction P using MvPolynomial.induction_on with
  | C r => exact ⟨0, by rw [sigma_C, evalN_C, mul_zero, add_zero]⟩
  | add P Q hP hQ =>
    obtain ⟨q₁, hq₁⟩ := hP
    obtain ⟨q₂, hq₂⟩ := hQ
    refine ⟨q₁ + q₂, ?_⟩
    rw [map_add, map_add, map_add, hq₁, hq₂]
    ring
  | mul_X P i hP =>
    obtain ⟨q, hq⟩ := hP
    refine ⟨q * (((a i : ℕ) : MvPolynomial (Fin k) A) + (p : MvPolynomial (Fin k) A) * X i) +
      C (evalN a P) * X i, ?_⟩
    rw [map_mul, map_mul, map_mul, sigma_X, evalN_X, map_natCast C (a i)]
    linear_combination
      (((a i : ℕ) : MvPolynomial (Fin k) A) + (p : MvPolynomial (Fin k) A) * X i) * hq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.exists_sigma_eq

open scoped Classical in
/-- The quotient by `p`, when it exists (and `0` otherwise). -/
noncomputable def divP {S : Type*} [CommRing S] (r : S) : S :=
  if h : ∃ q : S, r = (p : S) * q then h.choose else 0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.divP

theorem eq_mul_divP {S : Type*} [CommRing S] {r : S} (h : ∃ q : S, r = (p : S) * q) :
    r = (p : S) * divP p r := by
  rw [divP, dif_pos h]
  exact h.choose_spec

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.eq_mul_divP

/-- The substitution at a parameter `a ∈ F_p^k`. -/
def sigmaZ (a : Fin k → ZMod p) : MvPolynomial (Fin k) A →+* MvPolynomial (Fin k) A :=
  sigma p fun i => (a i).val

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.sigmaZ

variable {p}

/-- The digit map at the first-level parameter `a ∈ F_p^k`: `P ↦ π (P(a))`. -/
def dig (D : DigitData A p) (a : Fin k → ZMod p) : MvPolynomial (Fin k) A →+* ZMod p :=
  D.red.comp (evalN fun i => (a i).val)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.dig

/-- A polynomial with vanishing digit has a substitution divisible by `p`. -/
theorem exists_sigmaZ_eq_mul (D : DigitData A p) (a : Fin k → ZMod p)
    {P : MvPolynomial (Fin k) A} (hP : dig D a P = 0) :
    ∃ q : MvPolynomial (Fin k) A, sigmaZ p a P = (p : MvPolynomial (Fin k) A) * q := by
  obtain ⟨q, hq⟩ := exists_sigma_eq p (fun i => (a i).val) P
  obtain ⟨y, hy⟩ := D.exists_eq_mul (evalN (fun i => (a i).val) P) hP
  refine ⟨C y + q, ?_⟩
  show sigma p (fun i => (a i).val) P = _
  rw [hq, hy, map_mul, map_natCast C p, mul_add]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.exists_sigmaZ_eq_mul

/-- The embedding of digit vectors as constant polynomial vectors. -/
def castVec {n : ℕ} (e : Fin n → ZMod p) : Fin n → MvPolynomial (Fin k) A :=
  fun j => ((e j).val : MvPolynomial (Fin k) A)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.castVec

theorem dig_castVec [NeZero p] (D : DigitData A p) (a : Fin k → ZMod p) {n : ℕ}
    (e : Fin n → ZMod p) (j : Fin n) : dig D a (castVec e j) = e j := by
  show dig D a ((e j).val : MvPolynomial (Fin k) A) = e j
  rw [map_natCast, ZMod.natCast_zmod_val]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharZeroHost.dig_castVec

end CharZeroHost
end Metabelian
end BooneHigman
end GroupApproximation
