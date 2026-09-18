import GroupApproximation.BooneHigman.Metabelian.SuslinKillSwap
import GroupApproximation.Meta.AxiomGuard

/-!
# Killing primes, part 4: `Φ_N` is a ring automorphism of `A_{n+1}[X]`

Lane `bh-met-91t`.  `Φ_N = eval₂ ρ (X^N + C x_0)` and `Ψ_N = eval₂ ρ'_N (C x_0)` (see
`SuslinKillSwap`) are mutually inverse; both composites are checked on the generators
`C (C r)`, `C x_0`, `C x_{j+1}` and `X`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

variable (R : Type*) [CommRing R] (n : ℕ)

/-- `Φ_N`: `C a ↦ ρ a`, `X ↦ X^N + C x_0`. -/
noncomputable def suslinKill_phi (N : ℕ) :
    Polynomial (MvPolynomial (Fin (n + 1)) R) →+* Polynomial (MvPolynomial (Fin (n + 1)) R) :=
  Polynomial.eval₂RingHom (suslinKill_rho R n)
    (Polynomial.X ^ N + Polynomial.C (MvPolynomial.X 0))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_phi

/-- `Ψ_N`: `C a ↦ ρ'_N a`, `X ↦ C x_0`. -/
noncomputable def suslinKill_psi (N : ℕ) :
    Polynomial (MvPolynomial (Fin (n + 1)) R) →+* Polynomial (MvPolynomial (Fin (n + 1)) R) :=
  Polynomial.eval₂RingHom (suslinKill_rhoInv R n N) (Polynomial.C (MvPolynomial.X 0))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_psi

theorem suslinKill_phi_apply (N : ℕ) (p : Polynomial (MvPolynomial (Fin (n + 1)) R)) :
    suslinKill_phi R n N p =
      p.eval₂ (suslinKill_rho R n) (Polynomial.X ^ N + Polynomial.C (MvPolynomial.X 0)) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_phi_apply

theorem suslinKill_phi_C (N : ℕ) (a : MvPolynomial (Fin (n + 1)) R) :
    suslinKill_phi R n N (Polynomial.C a) = suslinKill_rho R n a := by
  rw [suslinKill_phi_apply, Polynomial.eval₂_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_phi_C

theorem suslinKill_phi_X (N : ℕ) :
    suslinKill_phi R n N Polynomial.X = Polynomial.X ^ N + Polynomial.C (MvPolynomial.X 0) := by
  rw [suslinKill_phi_apply, Polynomial.eval₂_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_phi_X

theorem suslinKill_psi_C (N : ℕ) (a : MvPolynomial (Fin (n + 1)) R) :
    suslinKill_psi R n N (Polynomial.C a) = suslinKill_rhoInv R n N a := by
  show Polynomial.eval₂ _ _ (Polynomial.C a) = _
  rw [Polynomial.eval₂_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_psi_C

theorem suslinKill_psi_X (N : ℕ) :
    suslinKill_psi R n N Polynomial.X = Polynomial.C (MvPolynomial.X 0) := by
  show Polynomial.eval₂ _ _ Polynomial.X = _
  rw [Polynomial.eval₂_X]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_psi_X

theorem suslinKill_phi_psi (N : ℕ) :
    (suslinKill_phi R n N).comp (suslinKill_psi R n N) = RingHom.id _ := by
  have hC : ((suslinKill_phi R n N).comp (suslinKill_psi R n N)).comp Polynomial.C =
      Polynomial.C := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, suslinKill_psi_C, suslinKill_rhoInv_C,
        suslinKill_phi_C, suslinKill_rho_C]
    · induction i using Fin.cases with
      | zero =>
        rw [RingHom.comp_apply, RingHom.comp_apply, suslinKill_psi_C, suslinKill_rhoInv_X0,
          map_sub, map_pow, suslinKill_phi_X, suslinKill_phi_C, suslinKill_rho_X0]
        ring
      | succ j =>
        rw [RingHom.comp_apply, RingHom.comp_apply, suslinKill_psi_C, suslinKill_rhoInv_Xs,
          suslinKill_phi_C, suslinKill_rho_Xs]
  refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
  · rw [RingHom.id_apply]
    exact RingHom.congr_fun hC a
  · rw [RingHom.comp_apply, suslinKill_psi_X, suslinKill_phi_C, suslinKill_rho_X0,
      RingHom.id_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_phi_psi

theorem suslinKill_psi_phi (N : ℕ) :
    (suslinKill_psi R n N).comp (suslinKill_phi R n N) = RingHom.id _ := by
  have hC : ((suslinKill_psi R n N).comp (suslinKill_phi R n N)).comp Polynomial.C =
      Polynomial.C := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
    · rw [RingHom.comp_apply, RingHom.comp_apply, suslinKill_phi_C, suslinKill_rho_C,
        suslinKill_psi_C, suslinKill_rhoInv_C]
    · induction i using Fin.cases with
      | zero =>
        rw [RingHom.comp_apply, RingHom.comp_apply, suslinKill_phi_C, suslinKill_rho_X0,
          suslinKill_psi_X]
      | succ j =>
        rw [RingHom.comp_apply, RingHom.comp_apply, suslinKill_phi_C, suslinKill_rho_Xs,
          suslinKill_psi_C, suslinKill_rhoInv_Xs]
  refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
  · rw [RingHom.id_apply]
    exact RingHom.congr_fun hC a
  · rw [RingHom.comp_apply, suslinKill_phi_X, map_add, map_pow, suslinKill_psi_X,
      suslinKill_psi_C, suslinKill_rhoInv_X0, RingHom.id_apply]
    ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_psi_phi

/-- The ring automorphism `Φ_N` of `A_{n+1}[X]`. -/
noncomputable def suslinKill_phiEquiv (N : ℕ) :
    Polynomial (MvPolynomial (Fin (n + 1)) R) ≃+* Polynomial (MvPolynomial (Fin (n + 1)) R) :=
  RingEquiv.ofRingHom (suslinKill_phi R n N) (suslinKill_psi R n N)
    (suslinKill_phi_psi R n N) (suslinKill_psi_phi R n N)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_phiEquiv

theorem suslinKill_phiEquiv_apply (N : ℕ) (p : Polynomial (MvPolynomial (Fin (n + 1)) R)) :
    suslinKill_phiEquiv R n N p =
      p.eval₂ (suslinKill_rho R n) (Polynomial.X ^ N + Polynomial.C (MvPolynomial.X 0)) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinKill_phiEquiv_apply

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
