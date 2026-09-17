import GroupApproximation.Manuscript.NonMF.RelatedBDL.Definitions
import GroupApproximation.Manuscript.NonMF.RelatedBDL.CornerInvolution
import GroupApproximation.Sofic.OperatorMF
import GroupApproximation.Sofic.HyperlinearReduction
import GroupApproximation.Algebra.MalcevLinear
import GroupApproximation.Stability.LinearMetricApproximation
import GroupApproximation.Sofic.UltraproductKazhdanTransport
import GroupApproximation.Manuscript.OneSidedMFRadical.HilbertSchmidtOperatorAction
import GroupApproximation.Analysis.PreliminaryInequalitiesPrinted
import GroupApproximation.Analysis.AmenableTraceHyperlinear
import GroupApproximation.Meta.AxiomGuard

/-!
# Related work: [BDL, Proposition 1.5]

Census row `9e2046c330c8`, `non_mf_groups_exist.tex` lines 351--353
(Related work):

> Bachner--Dogon--Lubotzky showed that for groups of Deligne type,
> operator--Hilbert--Schmidt stability would imply that the group is not
> MF~\cite[Proposition~1.5]{BDL}.

The endpoint `manuscriptSentence_deligneTypeOperatorHSStableNotMF` proves this
implication with no extra hypotheses: if `Γ` is of Deligne type
(`IsDeligneType`) and operator--Hilbert--Schmidt stable (`IsOperatorHSStable`),
then `Γ` is not MF (`IsOperatorMF`, the corpus notion of MF).

## Proof

Suppose `Γ` is MF, of Deligne type with central involution `J ∈ ker_RF(Γ)`,
and operator--HS stable.

1. **Operator approximation with `J ↦ −1`.** MF gives an injective
   representation `ρ : Γ → U(∏ M_{k_n} / ⊕ M_{k_n})`. Its image `u = ρ(J)` is
   a central self-adjoint unitary with `u ≠ 1`, so `q = ½(1 − u)` is a nonzero
   central projection. Compressing to the corner cut out by `q` gives an
   operator-norm asymptotic homomorphism `V_n : Γ → U(d_n)` with
   `‖V_n(J) + 1‖_op → 0`. This is
   `RelatedBDL.exists_opAsymptoticRep_of_injective_coronaRep`.
2. **Stability.** Stability gives genuine representations `ψ_n : Γ → U(d_n)`
   with `‖V_n(J) − ψ_n(J)‖_HS → 0`.
3. **Mal'cev.** Each `ψ_n(Γ)` is a finitely generated linear group, so it is
   residually finite. Every finite quotient of `ψ_n(Γ)` is a finite quotient of
   `Γ`, and `J` dies in all of those, so `ψ_n(J) = 1`
   (`unitary_hom_eq_one_of_forall_finite_quotient`).
4. **Contradiction.** For every matrix `V`,
   `2 = ‖2·1‖_HS ≤ ‖V + 1‖_HS + ‖1 − V‖_HS ≤ ‖V + 1‖_op + ‖V − 1‖_HS`
   (`two_le_opNorm_add_hsNorm_sub`). At `V = V_n(J)` the right side tends to
   `0 + 0`, which is a contradiction.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace RelatedBDL

open Filter Topology
open scoped Matrix.Norms.L2Operator

/-- The lower bound in step 4: `2 ≤ ‖V + 1‖_op + ‖V − 1‖_HS`. -/
theorem two_le_opNorm_add_hsNorm_sub (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) (V : Matrix Y Y ℂ) :
    2 ≤ ‖V + 1‖ + hsNorm Y (V - 1) := by
  have hone : hsNorm Y (1 : Matrix Y Y ℂ) = 1 := by
    unfold hsNorm
    rw [GroupApproximation.hsNormSq_one Y hY, Real.sqrt_one]
  have hsum : (V + 1) + (1 - V) = (2 : ℂ) • (1 : Matrix Y Y ℂ) := by
    rw [two_smul]
    abel
  have htwo : hsNorm Y ((2 : ℂ) • (1 : Matrix Y Y ℂ)) = 2 := by
    rw [OneSidedMFRadical.HilbertSchmidtOperatorAction.hsNorm_smul Y hY 2 1,
      Complex.norm_two, hone, mul_one]
  have htri :=
    OneSidedMFRadical.HilbertSchmidtOperatorAction.hsNorm_add_le Y hY (V + 1) (1 - V)
  rw [hsum, htwo] at htri
  have hop := PrelimNotation.hsNorm_le_l2_opNorm Y (V + 1)
  have hcomm := AmenableTraceHyperlinear.hsNorm_sub_comm Y 1 V
  linarith

/-- Step 3 (Mal'cev): if `J` dies in every finite quotient of a finitely
generated group `Γ`, then every finite-dimensional unitary representation
kills `J`. -/
theorem unitary_hom_eq_one_of_forall_finite_quotient {Γ : Type} [Group Γ]
    [Group.FG Γ] {J : Γ}
    (hJ : ∀ (F : Type) [Group F] [Finite F] (f : Γ →* F), f J = 1) (d : ℕ)
    (ψ : Γ →* Matrix.unitaryGroup (naturalFiniteModel d) ℂ) : ψ J = 1 := by
  by_contra hψ
  let ρ : Γ →* Matrix.GeneralLinearGroup (Fin d) ℂ := Unitary.toUnits.comp ψ
  have hρJ : ρ J ≠ 1 := by
    intro h
    apply hψ
    apply Unitary.toUnits_injective
    simpa [ρ] using h
  haveI : Group.ResiduallyFinite ρ.range :=
    MalcevLinear.residuallyFinite_of_fg ρ.range
      (LinearMetricApproximation.range_fg ρ)
  let y : ρ.range := ρ.rangeRestrict J
  have hy : y ≠ 1 := by
    intro h
    apply hρJ
    exact Subtype.ext_iff.mp h
  obtain ⟨N, hN⟩ := Group.exists_finiteIndexNormalSubgroup_notMem y hy
  letI := N.isNormal'
  letI := N.isFiniteIndex'
  have h := hJ (ρ.range ⧸ N.toSubgroup)
    ((QuotientGroup.mk' N.toSubgroup).comp ρ.rangeRestrict)
  apply hN
  exact (QuotientGroup.eq_one_iff y).mp (by simpa [y] using h)

/-- **[BDL, Proposition 1.5]**, `non_mf_groups_exist.tex` lines 351--353: for a
group of Deligne type, operator--Hilbert--Schmidt stability implies that the
group is not MF. -/
theorem manuscriptSentence_deligneTypeOperatorHSStableNotMF (Γ : Type)
    [Group Γ] (hD : IsDeligneType Γ) (hS : IsOperatorHSStable Γ) :
    ¬ IsOperatorMF Γ := by
  intro hMF
  obtain ⟨hfg, J, hJord, hJcent, hJrf⟩ := hD
  haveI : Group.FG Γ := hfg
  haveI : Countable Γ := GroupApproximation.countable_of_fg hfg
  have hJne : J ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hJord
    exact absurd hJord (by norm_num)
  have hJJ : J * J = 1 := by
    have h := pow_orderOf_eq_one J
    rw [hJord, pow_two] at h
    exact h
  obtain ⟨X, hX, rho0, hrho0⟩ := hMF
  haveI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  -- Step 1: the corner operator approximation with `V_n(J) ≈ −1`.
  let rho : Γ →* unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
    (normMatrixCoronaUnitaryEquiv X).toMonoidHom.comp rho0
  have hrho : Function.Injective rho :=
    (normMatrixCoronaUnitaryEquiv X).injective.comp hrho0
  obtain ⟨d, hd, V, hdef, hJclose⟩ :=
    exists_opAsymptoticRep_of_injective_coronaRep Γ X rho hrho J hJne hJJ hJcent
  -- Step 2: stability.
  obtain ⟨ψ, hψ⟩ := hS d hd V hdef
  -- Step 4, in the limit: eventually `‖V_k(J) + 1‖ + ‖V_k(J) − ψ_k(J)‖_HS < 2`.
  obtain ⟨k, hk⟩ := ((hJclose.add (hψ J)).eventually
    (gt_mem_nhds (show (0 : ℝ) + 0 < 2 by norm_num))).exists
  have hk2 : ‖(V k J : Matrix (naturalFiniteModel (d k))
        (naturalFiniteModel (d k)) ℂ) + 1‖ +
      hsNorm (naturalFiniteModel (d k))
        ((V k J : Matrix (naturalFiniteModel (d k))
            (naturalFiniteModel (d k)) ℂ) -
          (ψ k J : Matrix (naturalFiniteModel (d k))
            (naturalFiniteModel (d k)) ℂ)) < 2 := hk
  -- Step 3: `ψ_k(J) = 1`.
  have hψJ := unitary_hom_eq_one_of_forall_finite_quotient hJrf (d k) (ψ k)
  have hcoe : (ψ k J : Matrix (naturalFiniteModel (d k))
      (naturalFiniteModel (d k)) ℂ) = 1 := by
    simp [hψJ]
  rw [hcoe] at hk2
  have hlow := two_le_opNorm_add_hsNorm_sub (naturalFiniteModel (d k))
    (by simpa using hd k)
    (V k J : Matrix (naturalFiniteModel (d k)) (naturalFiniteModel (d k)) ℂ)
  linarith

end RelatedBDL
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedBDL.two_le_opNorm_add_hsNorm_sub
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedBDL.unitary_hom_eq_one_of_forall_finite_quotient
#audit_axioms GroupApproximation.Manuscript.NonMF.RelatedBDL.manuscriptSentence_deligneTypeOperatorHSStableNotMF
