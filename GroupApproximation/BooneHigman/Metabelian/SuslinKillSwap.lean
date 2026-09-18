import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Degree
import GroupApproximation.Meta.AxiomGuard

/-!
# Killing primes, part 3: the coordinate automorphism `Φ_N` of `A_{n+1}[X]`

Lane `bh-met-91t`.  `A_k = R[x_0, …, x_{k-1}]`, `fse : A_{n+1} ≃ A_n[x_0]` (Mathlib
`finSuccEquiv`).  With `ι : A_n → A_{n+1}`, `x_j ↦ x_{j+1}`, put
* `ρ : A_{n+1} → A_{n+1}[X]`, `x_0 ↦ X`, `x_{j+1} ↦ x_{j+1}` (namely `ρ = map ι ∘ fse`);
* `ρ' : A_{n+1} → A_{n+1}[X]`, `x_0 ↦ X - x_0^N`, `x_{j+1} ↦ x_{j+1}`;
* `Φ_N = eval₂ ρ (X^N + x_0)` and `Ψ_N = eval₂ ρ' x_0`, mutually inverse.
So `Φ_N` sends `x_0 ↦ X`, `X ↦ X^N + x_0`, and `ρ (fse⁻¹ q) = q.map ι`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

variable (R : Type*) [CommRing R] (n : ℕ)

/-- `ι : A_n → A_{n+1}`, `a ↦ fse⁻¹ (C a)`. -/
noncomputable def suslinKill_iota : MvPolynomial (Fin n) R →+* MvPolynomial (Fin (n + 1)) R :=
  (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv.toRingHom.comp Polynomial.C

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_iota

theorem suslinKill_fse_C (r : R) :
    MvPolynomial.finSuccEquiv R n (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_fse_C

theorem suslinKill_iota_X (j : Fin n) :
    suslinKill_iota R n (MvPolynomial.X j) = MvPolynomial.X j.succ := by
  show (MvPolynomial.finSuccEquiv R n).symm (Polynomial.C (MvPolynomial.X j)) = _
  rw [AlgEquiv.symm_apply_eq, MvPolynomial.finSuccEquiv_X_succ]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_iota_X

theorem suslinKill_iota_C (r : R) :
    suslinKill_iota R n (MvPolynomial.C r) = MvPolynomial.C r := by
  show (MvPolynomial.finSuccEquiv R n).symm (Polynomial.C (MvPolynomial.C r)) = _
  rw [AlgEquiv.symm_apply_eq, suslinKill_fse_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_iota_C

/-- `ρ = map ι ∘ fse`: `x_0 ↦ X`, `x_{j+1} ↦ C x_{j+1}`. -/
noncomputable def suslinKill_rho :
    MvPolynomial (Fin (n + 1)) R →+* Polynomial (MvPolynomial (Fin (n + 1)) R) :=
  (Polynomial.mapRingHom (suslinKill_iota R n)).comp
    (MvPolynomial.finSuccEquiv R n).toRingEquiv.toRingHom

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_rho

theorem suslinKill_rho_apply (p : MvPolynomial (Fin (n + 1)) R) :
    suslinKill_rho R n p = (MvPolynomial.finSuccEquiv R n p).map (suslinKill_iota R n) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_rho_apply

theorem suslinKill_rho_symm (q : Polynomial (MvPolynomial (Fin n) R)) :
    suslinKill_rho R n ((MvPolynomial.finSuccEquiv R n).symm q) = q.map (suslinKill_iota R n) :=
  by rw [suslinKill_rho_apply, AlgEquiv.apply_symm_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_rho_symm

theorem suslinKill_rho_X0 : suslinKill_rho R n (MvPolynomial.X 0) = Polynomial.X := by
  rw [suslinKill_rho_apply, MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_rho_X0

theorem suslinKill_rho_Xs (j : Fin n) :
    suslinKill_rho R n (MvPolynomial.X j.succ) = Polynomial.C (MvPolynomial.X j.succ) := by
  rw [suslinKill_rho_apply, MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C,
    suslinKill_iota_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_rho_Xs

theorem suslinKill_rho_C (r : R) :
    suslinKill_rho R n (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  rw [suslinKill_rho_apply, suslinKill_fse_C, Polynomial.map_C, suslinKill_iota_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_rho_C

/-- `ρ'_N`: `x_0 ↦ X - C x_0 ^ N`, `x_{j+1} ↦ C x_{j+1}`. -/
noncomputable def suslinKill_rhoInv (N : ℕ) :
    MvPolynomial (Fin (n + 1)) R →+* Polynomial (MvPolynomial (Fin (n + 1)) R) :=
  (Polynomial.eval₂RingHom (Polynomial.C.comp (suslinKill_iota R n))
      (Polynomial.X - Polynomial.C (MvPolynomial.X 0) ^ N)).comp
    (MvPolynomial.finSuccEquiv R n).toRingEquiv.toRingHom

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_rhoInv

theorem suslinKill_rhoInv_apply (N : ℕ) (p : MvPolynomial (Fin (n + 1)) R) :
    suslinKill_rhoInv R n N p = (MvPolynomial.finSuccEquiv R n p).eval₂
      (Polynomial.C.comp (suslinKill_iota R n))
      (Polynomial.X - Polynomial.C (MvPolynomial.X 0) ^ N) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_rhoInv_apply

theorem suslinKill_rhoInv_X0 (N : ℕ) : suslinKill_rhoInv R n N (MvPolynomial.X 0) =
    Polynomial.X - Polynomial.C (MvPolynomial.X 0) ^ N := by
  rw [suslinKill_rhoInv_apply, MvPolynomial.finSuccEquiv_X_zero, Polynomial.eval₂_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_rhoInv_X0

theorem suslinKill_rhoInv_Xs (N : ℕ) (j : Fin n) :
    suslinKill_rhoInv R n N (MvPolynomial.X j.succ) = Polynomial.C (MvPolynomial.X j.succ) := by
  rw [suslinKill_rhoInv_apply, MvPolynomial.finSuccEquiv_X_succ, Polynomial.eval₂_C,
    RingHom.comp_apply, suslinKill_iota_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_rhoInv_Xs

theorem suslinKill_rhoInv_C (N : ℕ) (r : R) :
    suslinKill_rhoInv R n N (MvPolynomial.C r) = Polynomial.C (MvPolynomial.C r) := by
  rw [suslinKill_rhoInv_apply, suslinKill_fse_C, Polynomial.eval₂_C, RingHom.comp_apply,
    suslinKill_iota_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_rhoInv_C

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
